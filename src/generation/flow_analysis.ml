open Batteries;;
open Jhupllib;;

open Parsetree;;

open Pdr_programming_continuation_extensions.Fragment_types;;
open Pdr_programming_utils.Variable_utils;;

type intermediate_var =
  { iv_name : Longident_value.t;
    iv_binder : Fragment_uid.t;
    iv_type : core_type option
        [@equal Pervasives.(=)] [@compare Pervasives.compare]
        [@printer Pp_utils.pp_option Pprintast.core_type];
    iv_bind_loc : Location.t
        [@equal Pervasives.(=)] [@compare Pervasives.compare]
        [@printer Location.print];
  }
[@@deriving eq, ord, show]
;;
let _ = show_intermediate_var;;

module Intermediate_var = struct
  type t = intermediate_var
  [@@deriving eq, ord, show]
  ;;
end;;

module Intermediate_var_set = struct
  module S = Set.Make(Intermediate_var);;
  include S;;
  include Pp_utils.Set_pp(S)(Intermediate_var);;
end;;

type fragment_group_intermediate_vars =
  Intermediate_var_set.t Fragment_uid_map.t
;;

module Fragment_uid_fragment_uid_multimap =
  Multimap.Make(Fragment_uid)(Fragment_uid)
;;

let create_reverse_uid_graph (group : fragment_group)
  : Fragment_uid_fragment_uid_multimap.t =
  group.fg_graph
  |> Fragment_uid_map.enum
  |> Enum.map
    (fun (uid, fragment) ->
       Enum.append
         (
           fragment.fragment_evaluation_holes
           |> List.enum
           |> Enum.map
             (fun evhd -> evhd.evhd_target_fragment)
         )
         (
           fragment.fragment_extension_holes
           |> List.enum
           |> Enum.map
             (fun exhd -> exhd.exhd_target_fragment)
         )
       |> Enum.filter_map (Option.map @@ fun uid' -> (uid',uid))
    )
  |> Enum.concat
  |> Fragment_uid_fragment_uid_multimap.of_enum
;;

type toposort_mark = Unmarked | In_progress | Complete;;
exception Cyclic_graph_in_topological_sort;;

let topological_sort (m : Fragment_uid_fragment_uid_multimap.t)
  : Fragment_uid.t list =
  let mark_map = ref (
      m
      |> Fragment_uid_fragment_uid_multimap.enum_by_key
      |> Enum.map (fun (uid,uids) ->
          Enum.append
            (Enum.singleton (uid,Unmarked))
            (uids
             |> Fragment_uid_fragment_uid_multimap.S.enum
             |> Enum.map (fun uid' -> (uid',Unmarked))
            )
        )
      |> Enum.concat
      |> Fragment_uid_map.of_enum
    )
  in
  let unmarked_set =
    ref @@ Fragment_uid_set.of_enum @@ Fragment_uid_map.keys !mark_map
  in
  let rec visit (n : Fragment_uid.t) : Fragment_uid.t Deque.t =
    match Fragment_uid_map.find n !mark_map with
    | Complete -> Deque.empty
    | In_progress -> raise Cyclic_graph_in_topological_sort
    | Unmarked ->
      unmarked_set := Fragment_uid_set.remove n !unmarked_set;
      mark_map := Fragment_uid_map.add n In_progress !mark_map;
      let results =
        Fragment_uid_fragment_uid_multimap.find n m
        |> Enum.map visit
        |> Enum.fold
          (fun a e -> Deque.append a e)
          Deque.empty
      in
      mark_map := Fragment_uid_map.add n Complete !mark_map;
      Deque.cons n results
  in
  let rec loop () : Fragment_uid.t Deque.t =
    if Fragment_uid_set.is_empty !unmarked_set then
      Deque.empty
    else begin
      let some_work =
        (visit (Enum.get_exn @@ Fragment_uid_set.enum !unmarked_set))
      in
      Deque.append some_work (loop ())
    end
  in
  List.of_enum @@ Deque.enum @@ loop ()
;;

let determine_intermediates (group : fragment_group)
  : fragment_group_intermediate_vars =
  (* To do this, we'll visit the nodes one by one, establishing a dictionary
     mapping UIDs to intermediate variable sets as we go.  As we begin to visit
     a node, its intermediate variable set will be complete.  (Note, for
     instance, that exit points in the graph always have empty intermediate
     variable sets.)  Visiting a node will augment the intermediate variable
     sets of all of its parent nodes.  Since we will have topologically sorted
     the fragment graph, all of this augmentation will be complete for a
     particular node before we visit it. *)
  let reverse_uid_graph = create_reverse_uid_graph group in
  let toposorted_uids = topological_sort reverse_uid_graph in
  let result_ivs_map =
    toposorted_uids
    |> List.fold_left
      (fun ivs_map visit_uid ->
         let inductive_ivs =
           Fragment_uid_map.find_default
             Intermediate_var_set.empty
             visit_uid
             ivs_map
         in
         let fragment =
           Fragment_uid_map.find
             visit_uid
             group.fg_graph
         in
         let immediate_ivs =
           fragment.fragment_externally_bound_variables
           |> Var_map.values
           |> Enum.map
             (fun ebv ->
                { iv_name = ebv.ebv_variable;
                  iv_binder = ebv.ebv_binder;
                  iv_type = ebv.ebv_type;
                  iv_bind_loc = ebv.ebv_bind_loc;
                }
             )
           |> Intermediate_var_set.of_enum
         in
         let ivs = Intermediate_var_set.union inductive_ivs immediate_ivs in
         let ivs_map' =
           reverse_uid_graph
           |> Fragment_uid_fragment_uid_multimap.find visit_uid
           |> Enum.fold
             (fun cur_ivs_map parent_uid ->
                let new_ivs_for_parent =
                  ivs
                  |> Intermediate_var_set.filter
                    (fun iv ->
                       not @@ Fragment_uid.equal iv.iv_binder parent_uid
                    )
                in
                let parent_ivs =
                  Intermediate_var_set.union new_ivs_for_parent
                    (Fragment_uid_map.find_default
                       Intermediate_var_set.empty
                       parent_uid
                       cur_ivs_map
                    )
                in
                Fragment_uid_map.add parent_uid parent_ivs cur_ivs_map
             ) ivs_map
         in
         ivs_map'
      )
      Fragment_uid_map.empty
  in
  result_ivs_map
  |> Fragment_uid_map.filter
    (fun _ v -> not @@ Intermediate_var_set.is_empty v)
;;
