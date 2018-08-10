open Batteries;;
open Jhupllib;;

open Pdr_programming_continuation_extensions.Fragment_types;;

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
