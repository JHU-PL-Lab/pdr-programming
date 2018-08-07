open Batteries;;
open Jhupllib;;
open OUnit2;;

open Asttypes;;
open Parsetree;;

open Pdr_programming_continuation_extensions;;
open Pdr_programming_transformation;;
open Pdr_programming_utils;;

(* ****************************************************************************
   Initialization and tooling
*)

let accumulated_tests = ref [];;
let add_test test = accumulated_tests := test::!accumulated_tests;;

(* ****************************************************************************
   Utilities
*)

let add_declaration_generation_test
    (name : string)
    (code : expression)
    (expected : structure)
  : unit =
  add_test (name >:: fun _ ->
      let open Fragment_types in
      let open Variable_utils in
      let result_group =
        code
        |> Transformer.do_transform
        |> Transformer_monad.run
          (Fragment_uid.new_context ())
          (new_fresh_variable_context ~prefix:"var" ())
          (fun (name,_) -> name.txt = "pop")
      in
      let spec =
        Continuation_types.create_continuation_type_spec result_group
      in
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
      assert_equal ~printer:(Pp_utils.pp_to_string Pprintast.structure)
        expected structure
    )
;;

(* ****************************************************************************
   Tests
*)

add_declaration_generation_test
  "single pop let binding"
  [%expr
    let x = [%pop] in
    x
  ]
  [%str
    type continuation =
      | Continuation_0
      | Continuation_1
  ]

(* ****************************************************************************
   Wiring and cleanup
*)

let tests = List.rev !accumulated_tests;;
