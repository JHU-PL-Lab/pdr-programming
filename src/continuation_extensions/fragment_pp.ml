(** This module provides pretty-printing routines for visualizing the fragment
    types.  Note that these routines invoke the code functions of the fragments;
    they should largely be used for debugging only. *)

open Format;;
open Parsetree;;
open Pprintast;;

open Batteries;;

open Jhupllib;;
open Pp_utils;;

open Pdr_programming_utils.Variable_utils;;

open Fragment_types;;

let box = pp_open_box;;
let ch = pp_print_char;;
let close = pp_close_box;;
let cut = pp_print_cut;;
let fspace = fun formatter () -> pp_print_char formatter ' ';;
let hvbox = pp_open_hvbox;;
let space = pp_print_space;;
let str = pp_print_string;;
let vbox = pp_open_vbox;;

let record_start f () =
  vbox f 0;
  str f "{ ";
  vbox f 0;
;;

let record_stop f () =
  close f ();
  cut f ();
  ch f '}';
  close f ();
;;

let record_item ?first:(first=false) f name value_printer value =
  if not first then space f ();
  hvbox f 2;
  str f name;
  fspace f ();
  ch f '=';
  space f ();
  value_printer f value;
  ch f ';';
  close f ();
;;

let pp_input_hole_data : input_hole_data pretty_printer = fun f ihd ->
  ignore ihd;
  str f "INPUT_HOLE";
;;

let pp_evaluation_hole_data : evaluation_hole_data pretty_printer = fun f ehd ->
  record_start f ();
  record_item ~first:true f "target_fragments" (pp_option Fragment_uid_set.pp)
    ehd.evhd_target_fragments;
  record_item f "bound_variables" (Var_map.pp @@ pp_option core_type)
    ehd.evhd_bound_variables;
  record_stop f ();
;;

let pp_extension_hole_data : extension_hole_data pretty_printer = fun f ehd ->
  record_start f ();
  record_item ~first:true f "extension" expression
    { pexp_desc = Pexp_extension ehd.exhd_extension;
      pexp_loc = ehd.exhd_loc;
      pexp_attributes = []
    };
  record_item f "target_fragment" (pp_option Fragment_uid.pp)
    ehd.exhd_target_fragment;
  record_item f "bound_variables" (Var_map.pp @@ pp_option core_type)
    ehd.exhd_bound_variables;
  record_stop f ();
;;

let pp_externally_bound_variable : externally_bound_variable pretty_printer =
  fun f ebv ->
    record_start f ();
    record_item ~first:true f "var" Longident_value.pp ebv.ebv_variable;
    record_item f "binder" Fragment_uid.pp ebv.ebv_binder;
    record_item f "type" (pp_option core_type) ebv.ebv_type;
    record_stop f ();
;;

let pp_fragment : fragment pretty_printer = fun f frag ->
  record_start f ();
  record_item ~first:true f "uid" Fragment_uid.pp frag.fragment_uid;
  record_item f "free_vars" Var_set.pp frag.fragment_free_variables;
  record_item f "ext_bound_vars"
    (Var_map.pp pp_externally_bound_variable)
    frag.fragment_externally_bound_variables;
  record_item f "input_hole" (pp_option pp_input_hole_data)
    frag.fragment_input_hole;
  record_item f "eval_holes" (pp_list pp_evaluation_hole_data)
    frag.fragment_evaluation_holes;
  record_item f "ext_holes" (pp_list pp_extension_hole_data)
    frag.fragment_extension_holes;
  record_item f "code" expression (
    frag.fragment_code
      (
        if Option.is_some frag.fragment_input_hole then
          Some [%expr INPUT_HOLE ]
        else
          None
      )
      (
        frag.fragment_evaluation_holes
        |> List.map (fun ehd expr ->
            let uid_str =
              ehd.evhd_target_fragments
              |> Option.map (Pp_utils.pp_to_string
                               (Pp_utils.pp_set
                                  Fragment_uid.pp Fragment_uid_set.enum))
              |> Option.default "None"
            in
            let uid_str_expr =
              { pexp_desc = Pexp_constant(Pconst_string(uid_str,None));
                pexp_loc = ehd.evhd_loc;
                pexp_attributes = [];
              }
            in
            [%expr EVAL_HOLE([%e uid_str_expr], [%e expr])]
          )
      )
      ( frag.fragment_extension_holes
        |> List.map (fun ehd ->
            let uid_str =
              ehd.exhd_target_fragment
              |> Option.map Fragment_uid.show
              |> Option.default "None"
            in
            let uid_str_expr =
              { pexp_desc = Pexp_constant(Pconst_string(uid_str,None));
                pexp_loc = ehd.exhd_loc;
                pexp_attributes = [];
              }
            in
            [%expr EXT_HOLE([%e uid_str_expr])]
          )
      )
  );
  record_stop f ();
;;

let pp_fragment_group : fragment_group pretty_printer = fun f fg ->
  record_start f ();
  record_item ~first:true f "graph"
    (pp_map Fragment_uid.pp pp_fragment Fragment_uid_map.enum)
    fg.fg_graph;
  record_item f "entry" Fragment_uid.pp fg.fg_entry;
  record_item f "exits" (pp_set Fragment_uid.pp Fragment_uid_set.enum)
    fg.fg_exits;
  record_stop f ();
;;

let string_of_fragment = pp_to_string pp_fragment;;

let string_of_fragment_group = pp_to_string pp_fragment_group;;
