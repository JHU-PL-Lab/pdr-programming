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
      assert_equal ~printer:(Pp_utils.pp_to_string (Pprintast.structure))
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
      | Continuation_fragment_1
  ]
;;

add_declaration_generation_test
  "continuation captures variable"
  [%expr
    let y : int = 4 in
    let x = [%pop] in
    y
  ]
  [%str
    type 'a2_ext_y_from_frag_1 continuation =
      | Continuation_fragment_2 of 'a2_ext_y_from_frag_1
  ]
;;

add_declaration_generation_test
  "continuation captures two variables"
  [%expr
    let y : int = 4 in
    let z : int = 5 in
    let x = [%pop] in
    (y,z)
  ]
  [%str
    type ('a5_ext_y_from_frag_2, 'a5_ext_z_from_frag_2)
      continuation =
      | Continuation_fragment_5 of 'a5_ext_y_from_frag_2 * 'a5_ext_z_from_frag_2
  ]
;;

add_declaration_generation_test
  "continuation captures one variable, avoids another"
  [%expr
    let y : int = 4 in
    let z : string = "5" in
    let x = [%pop] in
    y
  ]
  [%str
    type 'a3_ext_y_from_frag_2 continuation =
      | Continuation_fragment_3 of 'a3_ext_y_from_frag_2
  ]
;;

add_declaration_generation_test
  "continuation captures one variable, avoids another"
  [%expr
    let a : int = 4 in
    let b : string = "5" in
    let x = [%pop] in
    let c : char = 'c' in
    let y = [%pop] in
    (a,c)
  ]
  [%str
    type
      ('a4_inv_a_from_frag_2, 'a7_ext_a_from_frag_2, 'a7_ext_c_from_frag_4)
      continuation =
      | Continuation_fragment_4 of 'a4_inv_a_from_frag_2
      | Continuation_fragment_7 of 'a7_ext_a_from_frag_2 * 'a7_ext_c_from_frag_4
  ]
;;

(* ****************************************************************************
   Wiring and cleanup
*)

let tests = List.rev !accumulated_tests;;
