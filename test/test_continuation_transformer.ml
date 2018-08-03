open Batteries;;
open Jhupllib;;
open OUnit2;;

open Asttypes;;
open Parsetree;;

open Pdr_programming_continuation_extensions;;
open Pdr_programming_utils;;
open Pdr_programming_utils.Variable_utils;;

open Fragment_types;;

(* ****************************************************************************
   Initialization and tooling
*)

let accumulated_tests = ref [];;
let add_test test = accumulated_tests := test::!accumulated_tests;;

(* ****************************************************************************
   Expectation types
*)

let _ident_to_string i =
  match i with
  | Longident.Lident s -> s
  | _ -> raise @@ Utils.Invariant_failure "Don't know how to convert this!"
;;
let _bound_vars_map_to_list (x : core_type option Var_map.t)
  : (string * core_type option) list =
  x
  |> Var_map.enum
  |> Enum.map (fun (k,v) -> (_ident_to_string k, v))
  |> List.of_enum
;;
let _list_sorted_pervasive_eq a b =
  List.eq (=) (List.sort compare a) (List.sort compare b)
;;
let _list_sorted_pervasive_compare a b =
  List.compare compare (List.sort compare a) (List.sort compare b)
;;
let pp_core_type = Pprintast.core_type;;

type continuation_transform_test_output_expectation =
  { cttee_id : int option;
    cttee_extension : bool;
    cttee_bound_vars :
      (string * core_type option) list
        [@equal _list_sorted_pervasive_eq]
        [@compare _list_sorted_pervasive_compare];
  }
[@@deriving eq, ord, show]
;;

let pp_expression fmt e =
  Format.pp_print_string fmt @@ Pprintast.string_of_expression e
;;

type continuation_transform_test_fragment_expectation =
  { cttfe_id : int;
    cttfe_has_input : bool;
    cttfe_outputs : continuation_transform_test_output_expectation list
        [@equal _list_sorted_pervasive_eq]
        [@compare _list_sorted_pervasive_compare];
    cttfe_free_vars : string list
        [@equal _list_sorted_pervasive_eq]
        [@compare _list_sorted_pervasive_compare];
    cttfe_ext_bound_vars : (string * int * core_type option) list
        [@equal _list_sorted_pervasive_eq]
        [@compare _list_sorted_pervasive_compare];
    cttfe_code : expression [@equal fun _ _ -> true] [@compare fun _ _ -> 0 ];
  }
[@@deriving eq, ord, show]
;;

(** Describes the expectations of a continuation transformation test. *)
type continuation_transform_test_expectation =
  { ctte_entry : int;
    ctte_exits : int list;
    ctte_fragments : continuation_transform_test_fragment_expectation list;
  }
[@@deriving eq, ord, show]
;;

(* ****************************************************************************
   Utilities
*)

let convert_uid (uid : Fragment_uid.t) : int =
  int_of_string @@ Fragment_uid.show uid
;;

let convert_evaluation_hole (h : evaluation_hole_data)
  : continuation_transform_test_output_expectation =
  { cttee_id = Option.map convert_uid h.evhd_target_fragment;
    cttee_extension = false;
    cttee_bound_vars = _bound_vars_map_to_list h.evhd_bound_variables
  }
;;

let convert_extension_hole (h : extension_hole_data)
  : continuation_transform_test_output_expectation =
  { cttee_id = Option.map convert_uid h.exhd_target_fragment;
    cttee_extension = true;
    cttee_bound_vars = _bound_vars_map_to_list h.exhd_bound_variables
  }
;;

let convert_fragment (fragment : fragment)
  : continuation_transform_test_fragment_expectation =
  { cttfe_id = convert_uid fragment.fragment_uid;
    cttfe_has_input = Option.is_some fragment.fragment_input_hole;
    cttfe_outputs =
      List.map convert_evaluation_hole
        fragment.fragment_evaluation_holes @
      List.map convert_extension_hole
        fragment.fragment_extension_holes;
    cttfe_free_vars =
      fragment.fragment_free_variables
      |> Var_set.enum
      |> Enum.map _ident_to_string
      |> List.of_enum;
    cttfe_ext_bound_vars =
      fragment.fragment_externally_bound_variables
      |> Var_map.enum
      |> Enum.map
        (fun (k,(uid,cto)) -> (_ident_to_string k, convert_uid uid, cto))
      |> List.of_enum;
    cttfe_code =
      fragment.fragment_code
        (if Option.is_some fragment.fragment_input_hole
         then Some [%expr INPUT_HOLE]
         else None)
        (fragment.fragment_evaluation_holes
         |> List.map
           (fun eval_hole_data e ->
              let uid_str =
                eval_hole_data.evhd_target_fragment
                |> Option.map Fragment_uid.show
                |> Option.default "None"
              in
              let uid_str_expr =
                { pexp_desc = Pexp_constant(Pconst_string(uid_str,None));
                  pexp_loc = eval_hole_data.evhd_loc;
                  pexp_attributes = [];
                }
              in
              [%expr EVAL_HOLE([%e uid_str_expr],[%e e])]
           )
        )
        (fragment.fragment_extension_holes
         |> List.map
           (fun ext_hole_data ->
              let uid_str =
                ext_hole_data.exhd_target_fragment
                |> Option.map Fragment_uid.show
                |> Option.default "None"
              in
              let uid_str_expr =
                { pexp_desc = Pexp_constant(Pconst_string(uid_str,None));
                  pexp_loc = ext_hole_data.exhd_loc;
                  pexp_attributes = [];
                }
              in
              [%expr EXT_HOLE([%e uid_str_expr])]
           )
        )
  }
;;

let convert_fragment_group (group : fragment_group)
  : continuation_transform_test_expectation =
  { ctte_entry = convert_uid group.fg_entry;
    ctte_exits =
      List.map convert_uid @@ Fragment_uid_set.to_list group.fg_exits;
    ctte_fragments =
      Fragment_uid_map.values group.fg_graph
      |> Enum.map convert_fragment
      |> List.of_enum;
  }
;;

let canonicalize_expected_fragment x =
  { x with
    cttfe_outputs =
      List.sort compare_continuation_transform_test_output_expectation
        x.cttfe_outputs
  }
;;

let canonicalize_expected_group x =
  { x with
    ctte_fragments =
      List.sort
        compare_continuation_transform_test_fragment_expectation @@
      List.map canonicalize_expected_fragment x.ctte_fragments
  }
;;

(** Creates and registers a test of the fragment binding metadata routine. *)
let add_fragment_metadata_bind_test
    (name : string)
    (binder_uid : Fragment_uid.t)
    (bindings : core_type option Var_map.t)
    (fragment : fragment)
    (expected : continuation_transform_test_fragment_expectation)
  : unit =
  add_test (name >:: fun _ ->
      let result =
        Fragment_constructors.fragment_metadata_bind
          binder_uid bindings fragment
      in
      let cactual = canonicalize_expected_fragment @@ convert_fragment result in
      let cexpected = canonicalize_expected_fragment expected in
      assert_equal
        ~printer:show_continuation_transform_test_fragment_expectation
        cexpected cactual
    )
;;

(** Creates and registers a test of the non-binding embedding routine. *)
let add_embed_nonbind_test
    (name : string)
    (g1 : fragment_group)
    (g2 : fragment_group)
    (expected : continuation_transform_test_expectation)
  : unit =
  add_test (name >:: fun _ ->
      let result = Fragment_constructors.embed_nonbind Location.none g1 g2 in
      let cactual =
        canonicalize_expected_group @@ convert_fragment_group result
      in
      let cexpected =
        canonicalize_expected_group expected
      in
      assert_equal
        ~printer:show_continuation_transform_test_expectation
        cexpected cactual
    )
;;

(** Creates and registers a test of the continuation transformer.  The provided
    input expression is fed into the transformer.  The IDs used in the
    expectation must match the UIDs assigned by the framework.
*)
let add_continuation_transform_test
    (name : string)
    (input : expression)
    (expected : continuation_transform_test_expectation)
  : unit =
  add_test (name >:: fun _ ->
      (* Perform transformation *)
      let result =
        input
        |> Transformer.do_transform
        |> Transformer_monad.run
          (Fragment_types.Fragment_uid.new_context ())
          (Variable_utils.new_fresh_variable_context ~prefix:"var" ())
          (fun (name,_) -> name.txt = "pop")
      in
      (* Now verify the expectations of the result.  We can do this by
         converting the fragment group into an expectation (canonically sorting
         unsorted elements) and then inspecting everything in turn.  We'll start
         with conversion. *)
      let cactual =
        canonicalize_expected_group @@ convert_fragment_group result
      in
      let cexpected = canonicalize_expected_group expected in
      (* The expectation and the result are now both in a canonical form.  Now
         we just need to compare them! *)
      (* TODO: something with a bit more semantic aid to help the developer *)
      assert_equal ~printer:show_continuation_transform_test_expectation
        cexpected cactual
    )
;;

(* ****************************************************************************
   Tests
*)

let context = Fragment_uid.new_context () in
let uid = Fragment_uid.fresh ~context:context () in
add_fragment_metadata_bind_test
  "bind free x locally"
  uid
  (Var_map.singleton (Longident.Lident "x") None)
  { fragment_uid = uid;
    fragment_loc = Location.none;
    fragment_free_variables = Var_set.singleton (Longident.Lident "x");
    fragment_externally_bound_variables = Var_map.empty;
    fragment_input_hole = None;
    fragment_evaluation_holes =
      [ { evhd_loc = Location.none;
          evhd_target_fragment = None;
          evhd_bound_variables = Var_map.empty;
        }
      ];
    fragment_extension_holes = [];
    fragment_code = fun _ lst _ ->
      match lst with
      | [f] -> f [%expr x]
      | _ -> raise @@ Utils.Invariant_failure
          "non-singleton evaluation hole function list in text \"bind free x\""
  }
  { cttfe_id = 0;
    cttfe_has_input = false;
    cttfe_outputs = [
      { cttee_id = None;
        cttee_extension = false;
        cttee_bound_vars = [("x",None)]
      }
    ];
    cttfe_free_vars = [];
    cttfe_ext_bound_vars = [];
    cttfe_code = [%expr EVAL_HOLE("None", x)];
  }
;;

let context = Fragment_uid.new_context () in
let uid = Fragment_uid.fresh ~context:context () in
let uid' = Fragment_uid.fresh ~context:context () in
add_fragment_metadata_bind_test
  "bind free x externally"
  uid'
  (Var_map.singleton (Longident.Lident "x") None)
  { fragment_uid = uid;
    fragment_loc = Location.none;
    fragment_free_variables = Var_set.singleton (Longident.Lident "x");
    fragment_externally_bound_variables = Var_map.empty;
    fragment_input_hole = None;
    fragment_evaluation_holes =
      [ { evhd_loc = Location.none;
          evhd_target_fragment = None;
          evhd_bound_variables = Var_map.empty;
        }
      ];
    fragment_extension_holes = [];
    fragment_code = fun _ lst _ ->
      match lst with
      | [f] -> f [%expr x]
      | _ -> raise @@ Utils.Invariant_failure
          "non-singleton evaluation hole function list in test \"bind free x\""
  }
  { cttfe_id = 0;
    cttfe_has_input = false;
    cttfe_outputs = [
      { cttee_id = None;
        cttee_extension = false;
        cttee_bound_vars = [("x",None)]
      }
    ];
    cttfe_free_vars = [];
    cttfe_ext_bound_vars = [("x",convert_uid uid',None)];
    cttfe_code = [%expr EVAL_HOLE("None", x)];
  }
;;

(*
(* TODO: remove or rebuild this test.  It uses functions incorrectly. *)
let context = Fragment_uid.new_context () in
let uid1 = Fragment_uid.fresh ~context:context () in
let uid2 = Fragment_uid.fresh ~context:context () in
add_embed_nonbind_test
  "embed_nonbind with free variable"
  { fg_graph =
      Fragment_uid_map.singleton uid1
        { fragment_uid = uid1;
          fragment_loc = Location.none;
          fragment_free_variables = Var_set.singleton (Longident.Lident "x");
          fragment_externally_bound_variables = Var_map.empty;
          fragment_input_hole = None;
          fragment_evaluation_holes =
            [ { evhd_loc = Location.none;
                evhd_target_fragment = None;
                evhd_bound_variables = Var_map.empty;
              }
            ];
          fragment_extension_holes = [];
          fragment_code = fun _ lst _ ->
            match lst with
            | [f] -> f [%expr x]
            | _ -> raise @@ Utils.Invariant_failure (
                "non-singleton evaluation hole function list in test " ^
                "\"embed_nonbind with free variable\"")
        };
    fg_loc = Location.none;
    fg_entry = uid1;
    fg_exits = Fragment_uid_set.singleton uid1;
  }
  { fg_graph =
      Fragment_uid_map.singleton uid2
        { fragment_uid = uid2;
          fragment_loc = Location.none;
          fragment_free_variables = Var_set.empty;
          fragment_externally_bound_variables = Var_map.empty;
          fragment_input_hole = Some { inhd_loc = Location.none };
          fragment_evaluation_holes =
            [ { evhd_loc = Location.none;
                evhd_target_fragment = None;
                evhd_bound_variables = Var_map.empty;
              }
            ];
          fragment_extension_holes = [];
          fragment_code = fun inexpr_opt lst _ ->
            let inexpr = Option.get inexpr_opt in
            match lst with
            | [f] ->
              (* BUG: THIS IS NOT HOW WE USE EMBED_NONBIND! *)
              f [%expr let y = 4 in [%e inexpr] ]
            | _ -> raise @@ Utils.Invariant_failure (
                "non-singleton evaluation hole function list in test " ^
                "\"embed_nonbind with free variable\"")
        };
    fg_loc = Location.none;
    fg_entry = uid2;
    fg_exits = Fragment_uid_set.singleton uid2;
  }
  { ctte_entry = convert_uid uid2;
    ctte_exits = [convert_uid uid2];
    ctte_fragments =
      [ { cttfe_id = convert_uid uid2;
          cttfe_has_input = false;
          cttfe_outputs = [
            { cttee_id = None;
              cttee_extension = false;
              cttee_bound_vars = [("y",None)]
            }
          ];
          cttfe_free_vars = ["x"];
          cttfe_ext_bound_vars = [];
          cttfe_code = [%expr let y = 4 in EVAL_HOLE("None", x)];
        }
      ]

  }
;;
*)

add_continuation_transform_test
  "constant"
  [%expr 4 ]
  { ctte_entry = 0;
    ctte_exits = [0];
    ctte_fragments =
      [ { cttfe_id = 0;
          cttfe_has_input = false;
          cttfe_outputs = [
            { cttee_id = None; cttee_extension = false; cttee_bound_vars = [] }
          ];
          cttfe_free_vars = [];
          cttfe_ext_bound_vars = [];
          cttfe_code = [%expr EVAL_HOLE("None", 4) ];
        }
      ]
  }
;;

add_continuation_transform_test
  "variable"
  [%expr x ]
  { ctte_entry = 0;
    ctte_exits = [0];
    ctte_fragments =
      [ { cttfe_id = 0;
          cttfe_has_input = false;
          cttfe_outputs = [
            { cttee_id = None; cttee_extension = false; cttee_bound_vars = [] }
          ];
          cttfe_free_vars = ["x"];
          cttfe_ext_bound_vars = [];
          cttfe_code = [%expr EVAL_HOLE("None", x) ];
        }
      ]
  }
;;

add_continuation_transform_test
  "pure if-then-else"
  [%expr if true then 8 else 9 ]
  { ctte_entry = 3;
    ctte_exits = [3];
    ctte_fragments =
      [ { cttfe_id = 3;
          cttfe_has_input = false;
          cttfe_outputs = [
            { cttee_id = None; cttee_extension = false; cttee_bound_vars = [] };
            { cttee_id = None; cttee_extension = false; cttee_bound_vars = [] };
          ];
          cttfe_free_vars = [];
          cttfe_ext_bound_vars = [];
          cttfe_code =
            [%expr
              if true then EVAL_HOLE("None", 8) else EVAL_HOLE("None", 9)
            ];
        }
      ]
  }
;;

add_continuation_transform_test
  "pure let binding"
  [%expr let a = 0 in a]
  { ctte_entry = 1;
    ctte_exits = [1];
    ctte_fragments =
      [ { cttfe_id = 1;
          cttfe_has_input = false;
          cttfe_outputs = [
            { cttee_id = None; cttee_extension = false;
              cttee_bound_vars = [("a", None)]
            }
          ];
          cttfe_free_vars = [];
          cttfe_ext_bound_vars = [];
          cttfe_code = [%expr let a = 0 in EVAL_HOLE("None", a) ];
        }
      ]
  }
;;

add_continuation_transform_test
  "continuation extension"
  [%expr [%pop]]
  { ctte_entry = 0;
    ctte_exits = [0];
    ctte_fragments =
      [ { cttfe_id = 0;
          cttfe_has_input = false;
          cttfe_outputs = [
            { cttee_id = None; cttee_extension = true; cttee_bound_vars = [] }
          ];
          cttfe_free_vars = [];
          cttfe_ext_bound_vars = [];
          cttfe_code = [%expr EXT_HOLE("None") ];
        }
      ]
  }
;;

add_continuation_transform_test
  "impure let binding"
  [%expr let a = [%pop] in a]
  { ctte_entry = 0;
    ctte_exits = [1];
    ctte_fragments =
      [{ cttfe_id = 0; cttfe_has_input = false;
         cttfe_outputs =
           [{ cttee_id = (Some 1);
              cttee_extension = true;
              cttee_bound_vars = [];
            }
           ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code = [% expr EXT_HOLE "1" ];
       };
       { cttfe_id = 1; cttfe_has_input = true;
         cttfe_outputs =
           [{ cttee_id = None;
              cttee_extension = false;
              cttee_bound_vars = [("a",None)]
            }
           ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr let a = INPUT_HOLE  in EVAL_HOLE ("None", a)];
       }
      ]
  }
;;

add_continuation_transform_test
  "impure let binding with free variable in body"
  [%expr let a = [%pop] in b]
  { ctte_entry = 0;
    ctte_exits = [1];
    ctte_fragments =
      [{ cttfe_id = 0; cttfe_has_input = false;
         cttfe_outputs =
           [{ cttee_id = (Some 1);
              cttee_extension = true;
              cttee_bound_vars = [];
            }
           ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code = [% expr EXT_HOLE "1" ];
       };
       { cttfe_id = 1; cttfe_has_input = true;
         cttfe_outputs =
           [{ cttee_id = None;
              cttee_extension = false;
              cttee_bound_vars = [("a",None)]
            }
           ];
         cttfe_free_vars = ["b"];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr let a = INPUT_HOLE  in EVAL_HOLE ("None", b)];
       }
      ]
  }
;;

add_continuation_transform_test
  "impure let binding with external bind"
  [%expr let x = 4 in let y = [%pop] in x]
  { ctte_entry = 1;
    ctte_exits = [2];
    ctte_fragments =
      [{ cttfe_id = 1; cttfe_has_input = false;
         cttfe_outputs =
           [{ cttee_id = (Some 2);
              cttee_extension = true;
              cttee_bound_vars = [("x", None)];
            }
           ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code = [% expr let x = 4 in EXT_HOLE "2" ];
       };
       { cttfe_id = 2; cttfe_has_input = true;
         cttfe_outputs =
           [{ cttee_id = None;
              cttee_extension = false;
              cttee_bound_vars = [("x",None); ("y",None)]
            }
           ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [("x", 1, None)];
         cttfe_code = [%expr let y = INPUT_HOLE  in EVAL_HOLE ("None", x)];
       }
      ]
  }
;;

add_continuation_transform_test
  "pure single case match"
  [%expr
    match x with
    | Foo -> 0
  ]
  { ctte_entry = 2;
    ctte_exits = [2];
    ctte_fragments =
      [{ cttfe_id = 2; cttfe_has_input = false;
         cttfe_outputs = [
           { cttee_id = None; cttee_extension = false; cttee_bound_vars = [] }
         ];
         cttfe_free_vars = ["x"];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr
             match x with
             | Foo -> EVAL_HOLE("None", 0)
           ];
       }
      ]
  }
;;

add_continuation_transform_test
  "pure two case match"
  [%expr
    match x with
    | Foo -> 0
    | Bar -> 1
  ]
  { ctte_entry = 3;
    ctte_exits = [3];
    ctte_fragments =
      [{ cttfe_id = 3; cttfe_has_input = false;
         cttfe_outputs = [
           { cttee_id = None; cttee_extension = false; cttee_bound_vars = [] };
           { cttee_id = None; cttee_extension = false; cttee_bound_vars = [] };
         ];
         cttfe_free_vars = ["x"];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr
             match x with
             | Foo -> EVAL_HOLE("None", 0)
             | Bar -> EVAL_HOLE("None", 1)
           ];
       }
      ]
  }
;;

add_continuation_transform_test
  "immediately impure single case match"
  [%expr
    match x with
    | Foo -> [%pop]
  ]
  { ctte_entry = 2;
    ctte_exits = [2];
    ctte_fragments =
      [{ cttfe_id = 2; cttfe_has_input = false;
         cttfe_outputs = [
           { cttee_id = None; cttee_extension = true; cttee_bound_vars = [] }
         ];
         cttfe_free_vars = ["x"];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr
             match x with
             | Foo -> EXT_HOLE "None"
           ];
       }
      ]
  }
;;

add_continuation_transform_test
  "indirectly impure single case match"
  [%expr
    match a with
    | Foo ->
      let x = 4 in
      let y = [%pop] in
      x
  ]
  { ctte_entry = 4;
    ctte_exits = [3];
    ctte_fragments =
      [{ cttfe_id = 3; cttfe_has_input = true;
         cttfe_outputs = [
           { cttee_id = None;
             cttee_extension = false;
             cttee_bound_vars = [("x",None);("y",None)]
           }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr
             let y = INPUT_HOLE in
             EVAL_HOLE("None", x)
           ];
       };
       { cttfe_id = 4; cttfe_has_input = false;
         cttfe_outputs = [
           { cttee_id = Some 3;
             cttee_extension = true;
             cttee_bound_vars = [("x",None)]
           }
         ];
         cttfe_free_vars = ["a"];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr
             match x with
             | Foo -> let x = 4 in EXT_HOLE "3"
           ];
       }
      ]
  }
;;

add_continuation_transform_test
  "indirectly impure two case match"
  [%expr
    match x with
    | Foo ->
      let x = 3 in
      let y = [%pop] in
      x
    | Bar ->
      [%pop]
  ]
  { ctte_entry = 5;
    ctte_exits = [3; 5];
    ctte_fragments =
      [{ cttfe_id = 3; cttfe_has_input = true;
         cttfe_outputs = [
           { cttee_id = None;
             cttee_extension = false;
             cttee_bound_vars = [("x",None); ("y",None)]
           }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr
             let y = INPUT_HOLE in
             EVAL_HOLE("None", x)
           ];
       };
       { cttfe_id = 5; cttfe_has_input = false;
         cttfe_outputs = [
           { cttee_id = Some 3;
             cttee_extension = true;
             cttee_bound_vars = [("x",None)]
           };
           { cttee_id = None;
             cttee_extension = true;
             cttee_bound_vars = []
           }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr
             match x with
             | Foo -> let x = 3 in EXT_HOLE "3"
             | Bar -> EXT_HOLE "None"
           ];
       };
      ]
  }
;;

add_continuation_transform_test
  "pure tuple"
  [%expr (4, 8)]
  { ctte_entry = 2;
    ctte_exits = [2];
    ctte_fragments =
      [{ cttfe_id = 2; cttfe_has_input = false;
         cttfe_outputs = [
           {cttee_id = None; cttee_extension = false; cttee_bound_vars = [] }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr EVAL_HOLE("None", (4,8)) ];
       }
      ]
  }
;;

add_continuation_transform_test
  "impure tuple"
  [%expr ([%pop], 4)]
  { ctte_entry = 0;
    ctte_exits = [2];
    ctte_fragments =
      [{ cttfe_id = 0; cttfe_has_input = false;
         cttfe_outputs = [
           { cttee_id = Some 2;
             cttee_extension = true;
             cttee_bound_vars = []
           }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr EXT_HOLE "2" ];
       };
       { cttfe_id = 2; cttfe_has_input = true;
         cttfe_outputs = [
           { cttee_id = None;
             cttee_extension = false;
             cttee_bound_vars = [("var0",None)]
           }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr let var0 = INPUT_HOLE in EVAL_HOLE("None", (var0, 4)) ];
       }
      ]
  }
;;

add_continuation_transform_test
  "impure 4-tuple with pure let binding"
  [%expr (2, [%pop], 4, 5)]
  { ctte_entry = 1;
    ctte_exits = [4];
    ctte_fragments =
      [{ cttfe_id = 4; cttfe_has_input = true;
         cttfe_outputs = [
           { cttee_id = None;
             cttee_extension = false;
             cttee_bound_vars = [("var0", None); ("var1", None)]
           }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr
             let var0 = INPUT_HOLE in EVAL_HOLE("None", (var1, var0, 4, 5))
           ];
       };
       { cttfe_id = 1; cttfe_has_input = false;
         cttfe_outputs = [
           { cttee_id = Some 4;
             cttee_extension = true;
             cttee_bound_vars = [("var1", None)]
           }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr let var1 = 2 in EXT_HOLE "4" ];
       }
      ]
  }
;;

add_continuation_transform_test
  "pure function call"
  [%expr f x]
  { ctte_entry = 2;
    ctte_exits = [2];
    ctte_fragments =
      [{ cttfe_id = 2; cttfe_has_input = false;
         cttfe_outputs = [
           {cttee_id = None; cttee_extension = false; cttee_bound_vars = [] }
         ];
         cttfe_free_vars = ["f"; "x"];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr EVAL_HOLE("None", f x) ];
       }
      ]
  }
;;

add_continuation_transform_test
  "pure multi-argument function call"
  [%expr f x y]
  { ctte_entry = 3;
    ctte_exits = [3];
    ctte_fragments =
      [{ cttfe_id = 3; cttfe_has_input = false;
         cttfe_outputs = [
           {cttee_id = None; cttee_extension = false; cttee_bound_vars = [] }
         ];
         cttfe_free_vars = ["f"; "x"; "y"];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr EVAL_HOLE("None", f x y) ]
       }
      ]
  }
;;

add_continuation_transform_test
  "call impure function"
  [%expr [%pop] x]
  { ctte_entry = 0; ctte_exits = [2];
    ctte_fragments =
      [{ cttfe_id = 0; cttfe_has_input = false;
         cttfe_outputs = [
           { cttee_id = (Some 2);
             cttee_extension = true;
             cttee_bound_vars = []
           }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr EXT_HOLE "2" ];
       };
       { cttfe_id = 2; cttfe_has_input = true;
         cttfe_outputs = [
           { cttee_id = None;
             cttee_extension = false;
             cttee_bound_vars = [("var0", None)]
           }
         ];
         cttfe_free_vars = ["x"];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr let var0 = INPUT_HOLE in EVAL_HOLE ("None", (var0 x))];
       }
      ]
  }
;;

add_continuation_transform_test
  "call function with impure argument"
  [%expr f [%pop]]
  { ctte_entry = 1; ctte_exits = [2];
    ctte_fragments =
      [{ cttfe_id = 2; cttfe_has_input = true;
         cttfe_outputs = [
           { cttee_id = None;
             cttee_extension = false;
             cttee_bound_vars = [("var0", None);("var1", None)]
           }
         ];
         cttfe_free_vars = [];
         cttfe_ext_bound_vars = [];
         cttfe_code =
           [%expr let var0 = INPUT_HOLE in EVAL_HOLE ("None", (var1 var0)) ];
       };
       { cttfe_id = 1; cttfe_has_input = false;
         cttfe_outputs = [
           { cttee_id = (Some 2);
             cttee_extension = true;
             cttee_bound_vars = [("var1", None)]
           }
         ];
         cttfe_free_vars = ["f"];
         cttfe_ext_bound_vars = [];
         cttfe_code = [%expr let var1 = f  in EXT_HOLE "2" ];
       }
      ]
  }
;;

(* ****************************************************************************
   Wiring and cleanup
*)

let tests = List.rev !accumulated_tests;;
