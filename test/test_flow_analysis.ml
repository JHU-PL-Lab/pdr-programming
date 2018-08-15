open Batteries;;
open Jhupllib;;
open OUnit2;;

open Parsetree;;

open Pdr_programming_continuation_extensions;;
open Pdr_programming_generation;;
open Test_utils;;

(* ****************************************************************************
   Initialization and tooling
*)

let accumulated_tests = ref [];;
let add_test test = accumulated_tests := test::!accumulated_tests;;

(* ****************************************************************************
   Utilities
*)

let add_determine_intermediates_test
    (name : string)
    (code : expression)
    (expected : (int * ((string * int) list)) list)
  : unit =
  add_test (name >:: fun _ ->
      let open Fragment_types in
      let result_group = test_transform_code code in
      let intermediates = Flow_analysis.determine_intermediates result_group in
      let actual =
        intermediates
        |> Fragment_uid_map.enum
        |> Enum.map
          (fun (uid, ivs_set) ->
             ( int_of_uid uid,
               ivs_set
               |> Flow_analysis.Intermediate_var_set.enum
               |> Enum.map
                 (fun iv ->
                    string_of_ident iv.Flow_analysis.iv_name,
                    int_of_uid iv.Flow_analysis.iv_binder
                 )
               |> List.of_enum
             )
          )
        |> List.of_enum
      in
      assert_equal
        ~printer:(
          Pp_utils.pp_to_string @@
          Pp_utils.pp_list @@
          Pp_utils.pp_tuple Format.pp_print_int @@
          Pp_utils.pp_list @@
          Pp_utils.pp_tuple Format.pp_print_string Format.pp_print_int)
        expected actual
    )
;;

(* ****************************************************************************
   Tests
*)

add_determine_intermediates_test
  "pure let binding"
  [%expr let x = 4 in x ]
  []
;;

add_determine_intermediates_test
  "single step impure let binding"
  [%expr let x = 4 in let y = [%pop] in x]
  []
;;

add_determine_intermediates_test
  "double step impure let binding"
  [%expr let x = 4 in let y = [%pop] in let z = [%pop] in x]
  [(2,[("x",1)])]
;;

add_determine_intermediates_test
  "double step impure with condition"
  [%expr
    let x = 4 in
    let y = [%pop] in
    let z =
      if b then [%pop] else 5
    in
    x
  ]
  [(5,[("x",1)])]
;;

add_determine_intermediates_test
  "impure nested variable"
  [%expr
    let a = 4 in
    let x = [%pop] in
    let y =
      let a = 2 in
      let z = [%pop] in
      a
    in
    a
  ]
  [(3, [("a", 1)]); (4, [("a", 1)])]
  (* Even though fragment 4 (the innermost use of "a") has "a" externally bound
     by fragment 3 (the second fragment which binds "a" to "2"), it should also
     indicate that the "a" from fragment 1 (the entry fragment) is intermediate
     so we can convey that "a" to fragment 5 (the outermost use of "a"). *)
;;

(* ****************************************************************************
   Wiring and cleanup
*)

let tests = List.rev !accumulated_tests;;
