open Batteries;;
open Jhupllib;;
open OUnit2;;

open Asttypes;;
open Parsetree;;

module Big_variant = Pdr_programming_utils.Big_variant;;
module Pdr_utils = Pdr_programming_utils.Utils;;
open Pdr_programming_utils.Type_utils;;

(* ****************************************************************************
   Initialization and tooling
*)

let accumulated_tests = ref [];;
let add_test test = accumulated_tests := test::!accumulated_tests;;

(* ****************************************************************************
   Test utilities
*)

let pow b e =
  let rec loop acc n =
    if n = 0 then acc else loop (acc * b) (n - 1)
  in
  loop 1 e
;;

let constr_name_func i =
  Printf.sprintf "C%d" i
;;

let wrapper_name_func i s =
  Printf.sprintf "W%d_%s" i s
;;

let type_param_name_func i =
  "a" ^ string_of_int i
;;

let type_param_func i =
  { ptyp_desc = Ptyp_var (type_param_name_func i);
    ptyp_loc = Location.none;
    ptyp_attributes = [];
  }
;;

let structure_of_type_decls type_decls =
  type_decls
  |> List.map (fun type_decl ->
      { pstr_desc = Pstr_type(Recursive, [type_decl]);
        pstr_loc = Location.none
      }
    )
;;

let make_type_decl
    (type_name : string)
    (constructor_count : int)
    (constructor_spec_fn : int -> string * core_type list)
  : type_declaration =
  let constructor_declarations, tparam_names =
    0 --^ constructor_count
    |> Enum.map
      (fun i ->
         let name, param_types = constructor_spec_fn i in
         let constructor =
           { pcd_name = Location.mkloc name Location.none;
             pcd_args = Pcstr_tuple param_types;
             pcd_res = None;
             pcd_loc = Location.none;
             pcd_attributes = [];
           }
         in
         let tparam_names =
           param_types
           |> List.map tvars_of_type
           |> List.fold_left Tvar_set.union Tvar_set.empty
         in
         (constructor, tparam_names)
      )
    |> List.of_enum
    |> List.split
  in
  let tparams =
    tparam_names
    |> List.fold_left Tvar_set.union Tvar_set.empty
    |> Tvar_set.enum
    |> Enum.map
      (fun name ->
         let typ =
           { ptyp_desc = Ptyp_var name;
             ptyp_loc = Location.none;
             ptyp_attributes = [];
           }
         in
         (typ, Invariant)
      )
    |> List.of_enum
  in
  { ptype_name = Location.mkloc type_name Location.none;
    ptype_params = tparams;
    ptype_cstrs = [];
    ptype_kind = Ptype_variant constructor_declarations;
    ptype_private = Public;
    ptype_manifest = None;
    ptype_attributes = [];
    ptype_loc = Location.none;
  }
;;

let make_constant_type_decl
    (type_name : string)
    (start_index : int)
    (constructor_count : int)
  : type_declaration =
  make_type_decl
    type_name
    constructor_count
    (fun i -> (constr_name_func (i + start_index), []))
;;

let make_arg_type_decl
    (type_name : string)
    (start_index : int)
    (constructor_count : int)
    (arg_func : int -> core_type list)
  : type_declaration =
  make_type_decl
    type_name
    constructor_count
    (fun i -> (constr_name_func (i + start_index), arg_func (i + start_index)))
;;

let make_tparam_type_decl
    (type_name : string)
    (start_index : int)
    (constructor_count : int)
  : type_declaration =
  make_arg_type_decl
    type_name
    start_index
    constructor_count
    (fun i -> [ type_param_func i ] )
;;

let make_wrapper_type_decl
    (type_name : string)
    ~(name_digits : int)
    ~(level : int)
    ?param_counts:(param_counts_list=([] : int list))
    (start_index : int)
    (count : int)
  : type_declaration =
  make_type_decl
    type_name
    count
    (let param_counts = Array.of_list param_counts_list in
     fun i ->
       let index = start_index + i * pow 200 level in
       let index_str = string_of_int index in
       let padded_index_str = Pdr_utils.pad_string name_digits '0' index_str in
       let name = Printf.sprintf "W%d_%s" level padded_index_str in
       let arg_type_param_count, arg_type_start_index =
         if i < Array.length param_counts then
           ( param_counts.(i),
             List.fold_left (+) 0 @@ List.take i param_counts_list
           )
         else
           (0, 0)
       in
       let arg_type_params =
         arg_type_start_index --^ (arg_type_start_index + arg_type_param_count)
         |> Enum.map type_param_func
         |> List.of_enum
         |> List.sort Pervasives.compare
       in
       let arg_types =
         [ { ptyp_desc =
               Ptyp_constr(
                 Location.mkloc
                   (Longident.Lident(
                       Printf.sprintf "%s_%s" type_name padded_index_str))
                   Location.none,
                 arg_type_params);
             ptyp_loc = Location.none;
             ptyp_attributes = [];
           }
         ]
       in
       name, arg_types
    )
;;

(* ****************************************************************************
   Test creators
*)

let add_big_variant_type_test
    (name : string)
    (input : structure)
    (expected : structure)
  : unit =
  add_test (name >:: fun _ ->
      let type_decl =
        match input with
        | [ { pstr_desc = Pstr_type(_, [type_decl]); _ } ] -> type_decl
        | _ ->
          raise @@
          Utils.Invariant_failure "Expected variant type declaration in input"
      in
      let spec =
        Big_variant.create_big_variant
          ~wrapper_constructor_name_fn:wrapper_name_func
          type_decl
      in
      let types = Big_variant.create_big_variant_types spec in
      let expected_type_decls =
        expected
        |> List.map
          (fun item ->
             match item.pstr_desc with
             | Pstr_type(_, [type_decl]) -> type_decl
             | _ ->
               raise @@ Utils.Invariant_failure
                 "Expected variant type declarations in expectation"
          )
      in
      assert_equal
        ~printer:(fun (type_decl_list : type_declaration list) ->
            type_decl_list
            |> List.map
              (fun type_decl ->
                 { pstr_desc = Pstr_type(Recursive, [type_decl]);
                   pstr_loc = Location.none
                 }
              )
            |> Pp_utils.pp_to_string Pprintast.structure
          )
        expected_type_decls types
    )
;;

(* ****************************************************************************
   Tests
*)

add_big_variant_type_test
  "1 constant variant constructor"
  [%str type foo = C;; ]
[%str type foo = C;; ]
;;

add_big_variant_type_test
  "5 constant variant constructor"
  [%str type foo = A | B | C | D | E;; ]
[%str type foo = A | B | C | D | E;; ]
;;

add_big_variant_type_test
  "200 constant variant constructor"
  (structure_of_type_decls [make_constant_type_decl "foo" 0 200])
  (structure_of_type_decls [make_constant_type_decl "foo" 0 200])
;;

add_big_variant_type_test
  "201 constant variant constructor"
  (structure_of_type_decls [make_constant_type_decl "foo" 0 201])
  (structure_of_type_decls
     [ make_constant_type_decl "foo_000" 0 200;
       make_constant_type_decl "foo_200" 200 1;
       make_wrapper_type_decl "foo" ~name_digits:3 ~level:1 0 2;
     ]
  )
;;

add_big_variant_type_test
  "401 constant variant constructor"
  (structure_of_type_decls [make_constant_type_decl "foo" 0 401])
  (structure_of_type_decls
     [ make_constant_type_decl "foo_000" 0 200;
       make_constant_type_decl "foo_200" 200 200;
       make_constant_type_decl "foo_400" 400 1;
       make_wrapper_type_decl "foo" ~name_digits:3 ~level:1 0 3;
     ]
  )
;;

add_big_variant_type_test
  "40000 constant variant constructor"
  (structure_of_type_decls [make_constant_type_decl "foo" 0 40000])
  (structure_of_type_decls
     ( ( 0 --^ 200
         |> Enum.map
           (fun i ->
              make_constant_type_decl
                (Printf.sprintf "foo_%s"
                   (Pdr_utils.pad_string 5 '0' @@ string_of_int  @@ i * 200))
                (200 * i)
                200
           )
         |> List.of_enum
       ) @
       [ make_wrapper_type_decl "foo" ~name_digits:5 ~level:1 0 200;
       ]
     )
  )
;;

add_big_variant_type_test
  "40001 constant variant constructor"
  (structure_of_type_decls [make_constant_type_decl "foo" 0 40001])
  (structure_of_type_decls
     ( ( 0 --^ 200
         |> Enum.map
           (fun i ->
              make_constant_type_decl
                (Printf.sprintf "foo_00000_%s"
                   (Pdr_utils.pad_string 5 '0' @@ string_of_int  @@ i * 200))
                (200 * i)
                200
           )
         |> List.of_enum
       ) @
       [ make_wrapper_type_decl "foo_00000" ~name_digits:5 ~level:1 0 200;
         make_constant_type_decl "foo_40000_40000" 40000 1;
         make_wrapper_type_decl "foo_40000" ~name_digits:5 ~level:1 40000 1;
         make_wrapper_type_decl "foo" ~name_digits:5 ~level:2 0 2;
       ]
     )
  )
;;

add_big_variant_type_test
  "3 non-constant variant constructor"
  [%str type foo = A of int | B of int | C of int]
  [%str type foo = A of int | B of int | C of int]
;;

let type_fn i =
  (List.take (i mod 3 + 1)
     [ [%type: int]; [%type: string]; [%type: int list] ]
  )
in
add_big_variant_type_test
  "201 non-constant variant constructor"
  (structure_of_type_decls [ make_arg_type_decl "foo" 0 260 type_fn ])
  (structure_of_type_decls
     [ make_arg_type_decl "foo_000" 0 200 type_fn;
       make_arg_type_decl "foo_200" 200 60 type_fn;
       make_wrapper_type_decl "foo" ~name_digits:3 ~level:1 0 2;
     ]
  )
;;

add_big_variant_type_test
  "50 parametric variant constructor"
  (structure_of_type_decls [ make_tparam_type_decl "foo" 0 50 ])
  (structure_of_type_decls [ make_tparam_type_decl "foo" 0 50 ])
;;

add_big_variant_type_test
  "250 parametric variant constructor"
  (structure_of_type_decls [ make_tparam_type_decl "foo" 0 250 ])
  (structure_of_type_decls
     [ make_tparam_type_decl "foo_000" 0 200;
       make_tparam_type_decl "foo_200" 200 50;
       make_wrapper_type_decl
         "foo"
         ~name_digits:3
         ~level:1
         ~param_counts:[200;50]
         0 2;
     ]
  )
;;

(* ****************************************************************************
   Wiring and cleanup
*)

let tests = List.rev !accumulated_tests;;
