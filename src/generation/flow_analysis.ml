open Batteries;;
open Jhupllib;;

open Parsetree;;

open Pdr_programming_continuation_extensions.Fragment_types;;
open Pdr_programming_utils.Variable_utils;;

open Fragment_uid_graph;;

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
