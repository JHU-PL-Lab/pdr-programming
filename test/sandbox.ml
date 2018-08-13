open Batteries;;
open Jhupllib;;

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
  let expr =
    [%expr
      let y : int = 4 in
      let x = [%pop] in
      y
    ]
  in
  let open Fragment_types in
  let open Variable_utils in
  let result_group =
    expr
    |> Transformer.do_transform
    |> Transformer_monad.run
      (Fragment_uid.new_context ())
      (new_fresh_variable_context ~prefix:"var" ())
      (fun (name,_) -> name.txt = "pop")
  in
  let spec =
    Continuation_types.create_continuation_type_spec
      Location.none "continuation" result_group
  in
  let type_decls = Continuation_types.create_continuation_types spec in
  let structure =
    type_decls
    |> List.map
      (fun x ->
         { pstr_desc = Pstr_type(Recursive, [x]);
           pstr_loc = Location.none;
         }
      )
  in
  print_endline @@ Pp_utils.pp_to_string (Sandbox_crud.pp_structure) structure;
  print_endline @@ Pp_utils.pp_to_string (Pprintast.structure) structure
;;

(* main ();; *)

(* prerr_string @@ Fragment_pp.string_of_fragment_group @@
(Transformer_monad.run
   (Fragment_types.Fragment_uid.new_context ())
   (Variable_utils.new_fresh_variable_context ())
   (fun ext -> (fst ext).txt = "pop")
   (Transformer.do_transform e)
);
prerr_string "\n"; *)

let e =
  [%expr
    fun () ->
      let (x : stack_element) = [%pop] in
      let (y : stack_element) = [%pop] in
      let (z : stack_element) = [%pop] in
      [z;y;x]
  ]
;;

(* print_endline @@ Pp_utils.pp_to_string Pprintast.structure @@
[%str
  type stack_element = Num of int | Count of int
];;

print_endline @@ Pp_utils.pp_to_string Pprintast.structure @@
Continuation_code.generate_code_from_function e
;; *)

print_endline @@ Pp_utils.pp_to_string Sandbox_crud.pp_structure @@
[%str
  type stack_element = Foo | Bar of int | Bottom;;
  let%transition f a b =
    let x = [%pop] in
    (a,b,x)
;;
let helper x = x;;
];;
