open Batteries;;
open Jhupllib;;

open Asttypes;;
open Parsetree;;

open Pdr_programming_continuation_extensions;;
open Pdr_programming_transformation;;
open Pdr_programming_utils;;

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
                evhd_target_fragment = None;
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
  let open Fragment_types in
  (* let open Variable_utils in *)
  (* let rec loop n e =
    if n = 1 then e else
      loop (n-1) [%expr let x = [%pop] in [%e e]]
  in
  let expr = loop 5 [%expr x] in
  let result =
    expr
    |> Transformer.do_transform
    |> Transformer_monad.run
      (Fragment_uid.new_context ())
      (new_fresh_variable_context ~prefix:"var" ())
      (fun (name,_) -> name.txt = "pop")
     in *)
  let result = fabricate_group_for_linear_let 40001 in
  let spec = Continuation_types.create_continuation_type_spec result in
  let type_decls =
    Continuation_types.create_continuation_type_declarations
      Location.none
      "continuation"
      spec
  in
  let structure =
    type_decls
    |> List.map
      (fun x ->
         { pstr_desc = Pstr_type(Recursive, [x]);
           pstr_loc = Location.none;
         }
      )
  in
  let uids = List.of_enum @@ Fragment_uid_map.keys result.fg_graph in
  print_endline @@
  Pp_utils.pp_to_string (Pprintast.toplevel_phrase) (Ptop_def structure);
  print_endline @@
  Pp_utils.pp_to_string (Pprintast.expression) @@
  Continuation_types.call_constructor
    Location.none
    spec
    (List.nth uids 20000)
    []
;;

(* main ();; *)

print_endline @@
Pp_utils.pp_to_string (Pprintast.structure) @@
(
   [%str
     type t = Foo of (int)
   ]
);;
