(**
   This module contains a routine which, given a function definition
*)

open Batteries;;
open Jhupllib;;

open Location;;
open Asttypes;;
open Parsetree;;

open Pdr_programming_continuation_extensions;;
open Pdr_programming_utils.Variable_utils;;

open Continuation_types;;
open Flow_analysis;;
open Fragment_types;;

exception Invalid_transformation of string * Location.t;;

let mangle_intermediate_name (name : Longident.t) (binder_uid : Fragment_uid.t)
  : Longident.t =
  match name with
  | Longident.Lident s ->
    Longident.Lident(
      Printf.sprintf "__intermediate__%s__fragment_%s"
        s (Fragment_uid.show binder_uid))
  | _ ->
    raise @@
    Utils.Not_yet_implemented "mangle_intermediate_name: non-simple ident"
;;

let fragment_function_name (fragment_uid : Fragment_uid.t) : string =
  Printf.sprintf "__fragment_fn_%s" (Fragment_uid.show fragment_uid)
;;

type continuation_expression_function =
  Location.t -> Fragment_uid.t -> Fragment_uid.t -> expression
;;
type continuation_pattern_function =
  Location.t -> Fragment_uid.t -> pattern * Longident.t list
;;

let create_continuation_functions
  :
    fragment_group ->
    continuation_type_spec ->
    continuation_expression_function * continuation_pattern_function
  =
  fun fragment_group type_spec ->
    let intermediate_var_map =
      Flow_analysis.determine_intermediates fragment_group
    in
    let expr_fn =
      fun loc source_fragment_uid target_fragment_uid ->
        let target_fragment =
          Fragment_uid_map.find target_fragment_uid fragment_group.fg_graph
        in
        let target_intermediate_vars =
          Fragment_uid_map.find_default
            Intermediate_var_set.empty
            target_fragment_uid intermediate_var_map
        in
        let target_args =
          (* The target arguments should be:
               - the externally-bound variables of that fragment
               - the intermediate variables of that fragment *except* any which
                 are also external bindings
             We are building an expression to be used within the source
             fragment.  We don't care how the target fragment is going to use
             those variables or how it views them, so we can just lump them all
             into the same category here.
          *)
          let pass_vars : (Longident.t * Fragment_uid.t) list =
            Enum.append
              ( target_fragment.fragment_externally_bound_variables
                |> Var_map.values
                |> Enum.map
                  (fun ebv -> (ebv.ebv_variable, ebv.ebv_binder))
              )
              ( target_intermediate_vars
                |> Intermediate_var_set.enum
                |> Enum.filter
                  (fun iv ->
                     (* If this variable is also listed as an external binding,
                        then don't send an extra copy as an intermediate
                        variable; that's redundant. *)
                     let ebv_opt =
                       Var_map.Exceptionless.find
                         iv.iv_name
                         target_fragment.fragment_externally_bound_variables
                     in
                     match ebv_opt with
                     | None -> true
                     | Some ebv ->
                       not @@ Fragment_uid.equal ebv.ebv_binder iv.iv_binder
                  )
                |> Enum.map
                  (fun iv -> (iv.iv_name, iv.iv_binder))
              )
            |> List.of_enum
          in
          (* For each externally bound argument of the target fragment, one of
             two cases should occur: either the source fragment is the binder
             for that externally bound variable (in which case the variable at
             the continuation site should be used) or it is not (in which case
             this should be an intermediate variable for the source fragment and
             a name-mangled variable should be used).  There should never be a
             case in which the source fragment is neither the binder nor has an
             intermediate variable; that would indicate that the data flow
             analysis has failed. *)
          pass_vars
          |> List.enum
          |> Enum.map
            (fun (varname, var_binder) ->
               let varname' =
                 if Fragment_uid.equal var_binder source_fragment_uid then
                   varname
                 else
                   mangle_intermediate_name varname var_binder
               in
               { pexp_desc = Pexp_ident(mkloc varname' loc);
                 pexp_loc = loc;
                 pexp_attributes = [];
               }
            )
          |> List.of_enum
        in
        construct_continuation_value
          loc type_spec target_fragment_uid target_args
    in
    let pat_fn =
      fun loc target_fragment_uid ->
        let target_fragment =
          Fragment_uid_map.find target_fragment_uid fragment_group.fg_graph
        in
        let vars =
          let externally_bound_vars =
            target_fragment.fragment_externally_bound_variables
            |> Var_map.values
            |> Enum.map (fun ebv -> ebv.ebv_variable)
          in
          let intermediate_vars =
            intermediate_var_map
            |> Fragment_uid_map.find_default
              Intermediate_var_set.empty target_fragment_uid
            |> Intermediate_var_set.enum
            |> Enum.filter
              (fun iv ->
                 let ebv_opt =
                   Var_map.Exceptionless.find
                     iv.iv_name
                     target_fragment.fragment_externally_bound_variables
                 in
                 match ebv_opt with
                 | None -> true
                 | Some ebv ->
                   not @@ Fragment_uid.equal ebv.ebv_binder iv.iv_binder
              )
            |> Enum.map
              (fun iv -> mangle_intermediate_name iv.iv_name iv.iv_binder)
          in
          List.of_enum (Enum.append externally_bound_vars intermediate_vars)
        in
        let target_pats =
          vars
          |> List.enum
          |> Enum.map
            (fun varname ->
               match varname with
               | Longident.Lident(name) ->
                 { ppat_desc = Ppat_var(mkloc name loc);
                   ppat_loc = loc;
                   ppat_attributes = [];
                 }
               | _ ->
                 raise @@ Utils.Not_yet_implemented
                   (Printf.sprintf
                      "Passing non-simple identifier (%s) across continuations"
                      (Longident_value.show varname)
                   )
            )
          |> List.of_enum
        in
        ( destruct_continuation_value
            loc type_spec target_fragment_uid target_pats,
          vars
        )
    in
    (expr_fn, pat_fn)
;;

let map_evaluation_holes_to_functions
    (cont_pat_fn : continuation_pattern_function)
    (evhds : evaluation_hole_data list)
  : (expression -> expression) list =
  evhds
  |> List.map
    (fun evhd ->
       match evhd.evhd_target_fragment with
       | None ->
         (* This means that we don't need to continue; we just produce a
            result. *)
         fun value_expr -> [%expr Value_result([%e value_expr])]
       | Some target_fragment_uid ->
         let (_, vars) = cont_pat_fn evhd.evhd_loc target_fragment_uid in
         let call_tuple =
           { pexp_desc =
               Pexp_tuple(
                 vars
                 |> List.map
                   (fun var ->
                      { pexp_desc = Pexp_ident (mkloc var evhd.evhd_loc);
                        pexp_loc = evhd.evhd_loc;
                        pexp_attributes = [];
                      }
                   )
               );
             pexp_loc = evhd.evhd_loc;
             pexp_attributes = [];
           }
         in
         let frag_fn_name = fragment_function_name target_fragment_uid in
         let frag_fn_expr =
           { pexp_desc =
               Pexp_ident(
                 mkloc (Longident.Lident frag_fn_name) evhd.evhd_loc);
             pexp_loc = evhd.evhd_loc;
             pexp_attributes = [];
           }
         in
         fun value_expr ->
           [%expr [%e frag_fn_expr] [%e call_tuple] [%e value_expr]]
             [@metaloc evhd.evhd_loc]
    )
;;

let map_extension_holes_to_expressions
    (cont_expr_fn : continuation_expression_function)
    (source_fragment_uid : Fragment_uid.t)
    (exhds : extension_hole_data list)
  : expression list =
  exhds
  |> List.map
    (fun exhd ->
       match exhd.exhd_target_fragment with
       | None ->
         raise @@ Utils.Not_yet_implemented "Path terminates in [%pop]"
       | Some target_fragment_uid ->
         let cont_expr =
           cont_expr_fn
             exhd.exhd_loc
             source_fragment_uid
             target_fragment_uid
         in
         [%expr Continuation_result([%e cont_expr])]
    )
;;

let create_frag_fn_expr
    (loc : Location.t)
    (fragment_group : fragment_group)
    (cont_expr_fn : continuation_expression_function)
    (cont_pat_fn : continuation_pattern_function)
    (uid : Fragment_uid.t)
  : expression =
  let fragment = Fragment_uid_map.find uid fragment_group.fg_graph in
  let (_, vars) = cont_pat_fn loc uid in
  let frag_fn_cont_patterns =
    vars
    |> List.map
      (function
        | Longident.Lident s ->
          { ppat_desc = Ppat_var(mkloc s loc);
            ppat_loc = loc;
            ppat_attributes = [];
          }
        | _  ->
          raise @@
          Utils.Not_yet_implemented
            "non-simple ident in create_frag_fn_expr"
      )
  in
  let frag_fn_pat =
    match frag_fn_cont_patterns with
    | [] -> [%pat? ()] [@metaloc loc]
    | [pat] -> pat
    | _ ->
      { ppat_desc = Ppat_tuple(frag_fn_cont_patterns);
        ppat_loc = loc;
        ppat_attributes = [];
      }
  in
  let frag_fn_body =
    let eval_hole_fns =
      fragment.fragment_evaluation_holes
      |> map_evaluation_holes_to_functions cont_pat_fn
    in
    let ext_hole_exprs =
      fragment.fragment_extension_holes
      |> map_extension_holes_to_expressions cont_expr_fn uid
    in
    fragment.fragment_code (Some [%expr _input]) eval_hole_fns ext_hole_exprs
  in
  [%expr
    fun [%p frag_fn_pat] _input ->
      [%e frag_fn_body]
  ] [@metaloc loc]
;;

let create_frag_fn_decls
    (loc : Location.t)
    (fragment_group : fragment_group)
    (cont_expr_fn : continuation_expression_function)
    (cont_pat_fn : continuation_pattern_function)
  : structure_item =
  let frag_fn_bindings =
    fragment_group.fg_graph
    |> Fragment_uid_map.keys
    |> Enum.filter
      (fun uid -> not @@ Fragment_uid.equal uid fragment_group.fg_entry)
    |> Enum.map
      (fun uid ->
         let expr =
           create_frag_fn_expr loc fragment_group cont_expr_fn cont_pat_fn uid
         in
         let name = fragment_function_name uid in
         { pvb_pat = { ppat_desc = Ppat_var(mkloc name loc);
                       ppat_attributes = [];
                       ppat_loc = loc;
                     };
           pvb_expr = expr;
           pvb_attributes = [];
           pvb_loc = loc;
         }
      )
    |> List.of_enum
  in
  { pstr_desc = Pstr_value(Recursive, frag_fn_bindings);
    pstr_loc = loc;
  }
;;

let create_start_fn_decl
    (loc : Location.t)
    (fragment_group : fragment_group)
    (cont_expr_fn : continuation_expression_function)
    (cont_pat_fn : continuation_pattern_function)
    (start_fn_name : string)
    (function_of_body : expression -> expression)
  : structure_item =
  let start_fragment_uid = fragment_group.fg_entry in
  let start_fragment =
    fragment_group.fg_graph
    |> Fragment_uid_map.find start_fragment_uid
  in
  let evaluation_hole_expression_functions =
    start_fragment.fragment_evaluation_holes
    |> map_evaluation_holes_to_functions cont_pat_fn
  in
  let extension_hole_expressions =
    start_fragment.fragment_extension_holes
    |> map_extension_holes_to_expressions cont_expr_fn start_fragment_uid

  in
  let start_fun_body =
    start_fragment.fragment_code
      None
      evaluation_hole_expression_functions
      extension_hole_expressions
  in
  let start_fun_expr = function_of_body start_fun_body in
  { pstr_desc = Pstr_value(
        Nonrecursive,
        [ { pvb_pat =
              { ppat_desc = Ppat_var(mkloc start_fn_name loc);
                ppat_loc = loc;
                ppat_attributes = [];
              };
            pvb_expr = start_fun_expr;
            pvb_loc = loc;
            pvb_attributes = [];
          }
        ]
      );
    pstr_loc = loc;
  };;

let create_cont_fn_decl
    (loc : Location.t)
    (fragment_group : fragment_group)
    (continuation_type_name : string)
    (cont_fn_name : string)
    (cont_pat_fn : continuation_pattern_function)
  : structure_item =
  let extension_hole_targets =
    (* Only include those fragments which are targets of extension holes.
       Otherwise, we'll get branches that would never be reached which have
       type errors (due to the input not being an appropriate type).  This
       should work fine for the extension holes as the type of every pop is the
       same. *)
    fragment_group.fg_graph
    |> Fragment_uid_map.values
    |> Enum.map
      (fun fragment ->
         fragment.fragment_extension_holes
         |> List.enum
         |> Enum.filter_map (fun exhd -> exhd.exhd_target_fragment)
      )
    |> Enum.concat
    |> Fragment_uid_set.of_enum (* to eliminate duplicates *)
    |> Fragment_uid_set.enum
  in
  let cont_fn_cases =
    extension_hole_targets
    |> Enum.map
      (fun uid ->
         let (cont_pat, vars) = cont_pat_fn loc uid in
         let case_call_arg =
           match vars with
           | [] -> [%expr ()][@metaloc loc]
           | [var] ->
             { pexp_desc = Pexp_ident(mkloc var loc);
               pexp_loc = loc;
               pexp_attributes = [];
             }
           | _ ->
             { pexp_desc = Pexp_tuple(
                   vars
                   |> List.map
                     (fun var ->
                        { pexp_desc = Pexp_ident(mkloc var loc);
                          pexp_loc = loc;
                          pexp_attributes = [];
                        }
                     )
                 );
               pexp_loc = loc;
               pexp_attributes = [];
             }
         in
         let case_expr =
           { pexp_desc =
               Pexp_apply(
                 { pexp_desc =
                     Pexp_ident(mkloc
                                  (Longident.Lident(fragment_function_name uid))
                                  loc);
                   pexp_loc = loc;
                   pexp_attributes = [];
                 },
                 [ (Nolabel, case_call_arg);
                   (Nolabel, [%expr _input] [@metaloc loc]);
                 ]
               );
             pexp_loc = loc;
             pexp_attributes = [];
           }
         in
         { pc_lhs = cont_pat;
           pc_guard = None;
           pc_rhs = case_expr;
         }
      )
    |> List.of_enum
  in
  let cont_fn_body =
    { pexp_desc =
        Pexp_match([%expr _continuation][@metaloc loc], cont_fn_cases);
      pexp_loc = loc;
      pexp_attributes = [];
    }
  in
  let cont_fn =
    [%expr fun _continuation _input ->
      [%e cont_fn_body]
    ] [@metaloc loc]
  in
  let cont_type =
    { ptyp_desc =
        Ptyp_constr(mkloc (Longident.Lident continuation_type_name) loc, []);
      ptyp_loc = loc;
      ptyp_attributes = [];
    }
  in
  { pstr_desc =
      Pstr_value(
        Nonrecursive,
        [ { pvb_pat =
              { ppat_desc = Ppat_var(mkloc cont_fn_name loc);
                ppat_attributes = [];
                ppat_loc = loc;
              };
            pvb_expr =
              [%expr
                ([%e cont_fn] :
                   [%t cont_type] -> 'input -> 'a continuation_result)
              ];
            pvb_attributes = [];
            pvb_loc = loc;
          } ]);
    pstr_loc = loc;
  }
;;

(* Given a function expression, renames all of its parameters to fresh names and
   moves the binding of the original parameter names to the function body.  This
   has the effect of ensuring that all bindings in the original body of the
   function are either local let-bindings within the body or non-local bindings
   outside of the function.  This ensures that the body of a transition function
   needs no special handling to bind its parameters. *)
let rebind_parameters (function_expression : expression) : expression =
  let rec loop
      (wrap_fn : expression -> expression)
      (wrap_let : expression -> expression)
      (index : int)
      (expr : expression)
    : expression =
    match expr.pexp_desc with
    | Pexp_fun(arg_label, default_value, pattern, body) ->
      let new_name = Printf.sprintf "__parameter%d" index in
      let new_pattern =
        { pattern with
          ppat_desc = Ppat_var(mkloc new_name pattern.ppat_loc);
        }
      in
      let wrap_fn' e =
        wrap_fn @@
        { expr with
          pexp_desc = Pexp_fun(arg_label, default_value, new_pattern, e);
        }
      in
      let new_var_expr =
        { pexp_desc =
            Pexp_ident(mkloc (Longident.Lident new_name) pattern.ppat_loc);
          pexp_loc = pattern.ppat_loc;
          pexp_attributes = [];
        }
      in
      let wrap_let' e =
        wrap_let @@
        [%expr let [%p pattern] = [%e new_var_expr] in [%e e]]
          [@metaloc pattern.ppat_loc]
      in
      loop wrap_fn' wrap_let' (index + 1) body
    | _ ->
      wrap_fn @@ wrap_let expr
  in
  loop identity identity 1 function_expression
;;

(* Given a function expression, "unrolls" it to produce the function body, a
   list of patterns for its arguments (from left to right), and a function
   which, given a body, will reconstruct the function. *)
let rec unroll_function (e : expression)
  : expression * (expression -> expression) =
  match e.pexp_desc with
  | Pexp_fun(arg_label, default_value, pattern, body) ->
    let inner_body, reconstruct_fn = unroll_function body in
    (inner_body,
     fun new_body ->
       { e with
         pexp_desc = Pexp_fun(arg_label, default_value, pattern,
                              reconstruct_fn new_body);
       }
    )
  | _ -> (e, (fun new_body -> new_body))
;;

let generate_code_from_function
    ?continuation_type_name:(continuation_type_name = "continuation")
    ?start_fn_name:(start_fn_name = "start")
    ?cont_fn_name:(cont_fn_name = "cont")
    (func_expr : expression)
  : structure =
  let func_expr' = rebind_parameters func_expr in
  let func_body, func_reconstruct = unroll_function func_expr' in
  let loc = func_expr.pexp_loc in
  let fragment_group =
    func_body
    |> Transformer.do_transform
    |> Transformer_monad.run
      (Fragment_types.Fragment_uid.new_context ())
      (new_fresh_variable_context ())
      (fun ext -> (fst ext).txt = "pop")
  in
  let type_spec =
    create_continuation_type_spec loc continuation_type_name fragment_group
  in
  let cont_expr_fn, cont_pat_fn =
    create_continuation_functions fragment_group type_spec
  in
  let type_decls =
    (* TODO: ppx_deriving attributes *)
    create_continuation_types type_spec
    |> List.map
      (fun type_decl ->
         { pstr_desc = Pstr_type(Recursive, [type_decl]);
           pstr_loc = loc;
         }
      )
  in
  let result_type_decl =
    let typ =
      { ptyp_desc =
          Ptyp_constr(mkloc (Longident.Lident continuation_type_name) loc, []);
        ptyp_loc = loc;
        ptyp_attributes = [];
      }
    in
    [%str
      type 'a continuation_result =
        | Value_result of 'a
        | Continuation_result of [%t typ]
    ] (* FIXME: these types still aren't quite right: continuation results must
         be monadic too, so it seems the result should be within the monad or
         something. *)
  in
  let frag_fn_decls =
    create_frag_fn_decls loc fragment_group cont_expr_fn cont_pat_fn
  in
  let cont_fn_decl =
    create_cont_fn_decl
      loc
      fragment_group
      continuation_type_name
      cont_fn_name
      cont_pat_fn
  in
  let start_fn_decl =
    create_start_fn_decl
      loc
      fragment_group
      cont_expr_fn
      cont_pat_fn
      start_fn_name
      func_reconstruct
  in
  type_decls @
  result_type_decl @
  [frag_fn_decls] @
  [start_fn_decl] @
  [cont_fn_decl]
;;
