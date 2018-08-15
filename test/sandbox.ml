open Batteries;;
(* open Jhupllib;; *)

(* open Asttypes;; *)
(* open Parsetree;; *)

open Pdr_programming_continuation_extensions;;
open Pdr_programming_generation;;
open Pdr_programming_utils;;

open Sandbox_crud;;

let fabricate_group_for_linear_let n =
  let open Fragment_types in
  let open Variable_utils in
  let context = Fragment_uid.new_context () in
  let uids =
    1 -- n
    |> Enum.map
      (fun _ -> Fragment_uid.fresh ~context:context ())
    |> List.of_enum
  in
  let uid_pairs =
    uids
    |> List.tl
    |> List.combine (List.take (List.length uids - 1) uids)
  in
  let top_fragment =
    uid_pairs
    |> List.hd
    |> (fun (uid1,uid2) ->
        let ext = (Location.mkloc "pop" Location.none, PStr []) in
        { fragment_uid = uid1;
          fragment_loc = Location.none;
          fragment_free_variables = Var_set.empty;
          fragment_externally_bound_variables = Var_map.empty;
          fragment_input_hole = None;
          fragment_evaluation_holes = [];
          fragment_extension_holes =
            [ { exhd_extension = ext;
                exhd_loc = Location.none;
                exhd_target_fragment = Some(uid2);
                exhd_bound_variables = Var_map.empty;
              }
            ];
          fragment_code = fun _ _ es -> List.hd es
        }
      )
  in
  let inductive_fragments =
    uid_pairs
    |> List.tl
    |> List.map
      (fun (uid1,uid2) ->
         let ext = (Location.mkloc "pop" Location.none, PStr []) in
         let x = Longident.Lident "x" in
         { fragment_uid = uid1;
           fragment_loc = Location.none;
           fragment_free_variables = Var_set.empty;
           fragment_externally_bound_variables = Var_map.empty;
           fragment_input_hole = Some({ inhd_loc = Location.none });
           fragment_evaluation_holes = [];
           fragment_extension_holes =
             [ { exhd_extension = ext;
                 exhd_loc = Location.none;
                 exhd_target_fragment = Some(uid2);
                 exhd_bound_variables = Var_map.singleton x None;
               }
             ];
           fragment_code =
             fun ieo _ es ->
               [%expr let x = [%e Option.get ieo] in [%e List.hd es]]
         }
      )
  in
  let bottom_fragment =
    uids
    |> List.last
    |> (fun uid ->
        let x = Longident.Lident "x" in
        { fragment_uid = uid;
          fragment_loc = Location.none;
          fragment_free_variables = Var_set.empty;
          fragment_externally_bound_variables = Var_map.empty;
          fragment_input_hole = Some({ inhd_loc = Location.none });
          fragment_evaluation_holes =
            [ { evhd_loc = Location.none;
                evhd_target_fragments = None;
                evhd_bound_variables = Var_map.singleton x None;
              }
            ];
          fragment_extension_holes = [];
          fragment_code =
            fun ieo ef _ ->
              let e = List.hd ef [%expr x] in
              [%expr let x = [%e Option.get ieo] in [%e e]]
        }
      )
  in
  let fragments = top_fragment :: (inductive_fragments @ [bottom_fragment]) in
  let tagged_fragments = List.combine uids fragments in
  { fg_graph = Fragment_uid_map.of_enum @@ List.enum tagged_fragments;
    fg_loc = Location.none;
    fg_entry = List.hd uids;
    fg_exits = Fragment_uid_set.singleton @@ List.last uids;
  }
;;

let main () =
  let expr =
    [%expr
      fun (a : int) ->
        let%pick (z : t) = List.enum [A;B;C 1;C 2] in
        let%require C (y : int) = z in
        let _ = [%pop] in
        [%pick_lazy
          (a,y);
          (y,a)
        ]
    ]
  in
  Continuation_code.generate_code_from_function expr
;;

main ();;
