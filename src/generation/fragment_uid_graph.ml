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
             (fun evhd ->
                match evhd.evhd_target_fragments with
                | None -> Enum.empty ()
                | Some target_fragments ->
                  Fragment_uid_set.enum target_fragments
             )
           |> Enum.concat
         )
         (
           fragment.fragment_extension_holes
           |> List.enum
           |> Enum.filter_map
             (fun exhd -> exhd.exhd_target_fragment)
         )
       |> Enum.map (fun uid' -> (uid',uid))
    )
  |> Enum.concat
  |> Fragment_uid_fragment_uid_multimap.of_enum
;;

type toposort_mark = Unmarked | In_progress | Complete;;
exception Cyclic_graph_in_topological_sort;;

let topological_sort (m : Fragment_uid_fragment_uid_multimap.t)
  : Fragment_uid.t list =
  let all_uids =
    m
    |> Fragment_uid_fragment_uid_multimap.enum_by_key
    |> Enum.map
      (fun (uid,uids) ->
         Enum.append (Enum.singleton uid) @@
         Fragment_uid_fragment_uid_multimap.S.enum uids
      )
    |> Enum.concat
    |> Fragment_uid_set.of_enum
  in
  let initial_mark_state =
    all_uids
    |> Fragment_uid_set.enum
    |> Enum.map (fun uid -> (uid,Unmarked))
    |> Fragment_uid_map.of_enum
  in
  let rec visit unmarked_set mark_map result_list uid =
    let mark = Fragment_uid_map.find uid mark_map in
    match mark with
    | Complete -> (unmarked_set, mark_map, result_list)
    | In_progress -> raise Cyclic_graph_in_topological_sort
    | Unmarked ->
      let mark_map' = Fragment_uid_map.add uid In_progress mark_map in
      let unmarked_set' = Fragment_uid_set.remove uid unmarked_set in
      let (unmarked_set'', mark_map'',result_list'') =
        Fragment_uid_fragment_uid_multimap.find uid m
        |> Enum.fold
          (fun (us,mm,rl) uid' -> visit us mm rl uid')
          (unmarked_set', mark_map', result_list)
      in
      let mark_map''' = Fragment_uid_map.add uid Complete mark_map'' in
      let result_list''' = uid :: result_list'' in
      (unmarked_set'', mark_map''', result_list''')
  in
  let rec loop unmarked_set mark_map result_list =
    if Fragment_uid_set.is_empty unmarked_set then result_list else
      let uid =
        Enum.get_exn @@ Fragment_uid_set.enum unmarked_set
      in
      let (unmarked_set',mark_map',result_list') =
        visit unmarked_set mark_map result_list uid
      in
      loop unmarked_set' mark_map' result_list'
  in
  loop all_uids initial_mark_state []
;;
