(**
   This module contains a routine which, given a function definition
*)

open Batteries;;
open Jhupllib;;

open Location;;
open Asttypes;;
open Parsetree;;

open Pdr_programming_continuation_extensions;;
open Pdr_programming_utils.Ast_utils;;
open Pdr_programming_utils.Variable_utils;;

open Continuation_types;;
open Flow_analysis;;
open Fragment_types;;

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

type continuation_operations =
  {
    co_expression :
      Location.t -> Fragment_uid.t -> Fragment_uid.t -> expression;
    co_argument_expressions :
      Location.t -> Fragment_uid.t -> Fragment_uid.t -> expression list;
    co_pattern :
      Location.t -> Fragment_uid.t -> pattern;
    co_pattern_variables :
      Fragment_uid.t -> Longident.t list;
  }
;;

let process_nondeterminism_extensions (expression : expression) =
  let mapper =
    { Ast_mapper.default_mapper with
      expr = fun mapper e ->
        match e with
        | [%expr let%pick [%p? val_pat] = [%e? val_expr] in [%e? body]] ->
          let val_expr' = mapper.expr mapper val_expr in
          let body' = mapper.expr mapper body in
          [%expr
            BatEnum.concat
              (BatEnum.map (fun [%p val_pat] -> [%e body']) [%e val_expr'])
          ] [@metaloc e.pexp_loc]
        | [%expr let%require [%p? val_pat] = [%e? val_expr] in [%e? body]] ->
          let val_expr' = mapper.expr mapper val_expr in
          let body' = mapper.expr mapper body in
          [%expr
            match [%e val_expr'] with
            | [%p val_pat] -> [%e body']
            | _ -> BatEnum.empty ()
          ] [@metaloc e.pexp_loc]
        | [%expr let%antirequire [%p? val_pat] = [%e? val_expr] in [%e? body]]->
          let val_expr' = mapper.expr mapper val_expr in
          let body' = mapper.expr mapper body in
          [%expr
            match [%e val_expr'] with
            | [%p val_pat] -> BatEnum.empty ()
            | _ -> [%e body']
          ] [@metaloc e.pexp_loc]
        | _ ->
          Ast_mapper.default_mapper.expr mapper e
    }
  in
  mapper.expr mapper expression
;;

let create_continuation_operations
  : fragment_group -> continuation_type_spec -> continuation_operations =
  fun fragment_group type_spec ->
    let intermediate_var_map =
      Flow_analysis.determine_intermediates fragment_group
    in
    let expr_args_fn =
      fun loc source_fragment_uid target_fragment_uid ->
        let source_fragment =
          Fragment_uid_map.find source_fragment_uid fragment_group.fg_graph
        in
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
                 let source_is_binder =
                   Fragment_uid.equal var_binder source_fragment_uid
                 in
                 let externally_bound_for_source =
                   let external_binder =
                     source_fragment.fragment_externally_bound_variables
                     |> Var_map.Exceptionless.find varname
                   in
                   match external_binder with
                   | None -> false
                   | Some ebv ->
                     Fragment_uid.equal var_binder ebv.ebv_binder
                 in
                 if source_is_binder || externally_bound_for_source then
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
        target_args
    in
    let pat_fn =
      fun target_fragment_uid ->
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
        vars
    in
    {
      co_expression =
        (fun loc source_fragment_uid target_fragment_uid ->
           let target_args =
             expr_args_fn loc source_fragment_uid target_fragment_uid
           in
           construct_continuation_value
             loc type_spec target_fragment_uid target_args
        );
      co_argument_expressions =
        (fun loc source_fragment_uid target_fragment_uid ->
           expr_args_fn loc source_fragment_uid target_fragment_uid
        );
      co_pattern =
        (fun loc target_fragment_uid ->
           let target_pats =
             pat_fn target_fragment_uid
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
           destruct_continuation_value
             loc type_spec target_fragment_uid target_pats
        );
      co_pattern_variables =
        (fun target_fragment_uid ->
           pat_fn target_fragment_uid
        );
    }
;;

let map_evaluation_holes_to_functions
    (ops : continuation_operations)
    (source_fragment_uid : Fragment_uid.t)
    (evhds : evaluation_hole_data list)
  : (expression -> expression) list =
  evhds
  |> List.map
    (fun evhd ->
       match evhd.evhd_target_fragments with
       | None ->
         (* This means that we don't need to continue; we just produce a
            result. *)
         fun value_expr ->
           [%expr BatEnum.singleton(Value_result([%e value_expr]))]
       | Some target_fragment_uids ->
         let expr_fns =
           target_fragment_uids
           |> Fragment_uid_set.enum
           |> Enum.map (fun target_fragment_uid ->
               let var_exprs =
                 ops.co_argument_expressions
                   evhd.evhd_loc source_fragment_uid target_fragment_uid
               in
               let vars_arg = expression_pseudo_tuple evhd.evhd_loc var_exprs in
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
                 [%expr [%e frag_fn_expr] [%e vars_arg] [%e value_expr]]
                   [@metaloc evhd.evhd_loc]
             )
           |> List.of_enum
         in
         match expr_fns with
         | [] ->
           raise @@ Utils.Invariant_failure
             "evaluation hole with Some empty exit point list"
         | [expr_fn] -> expr_fn
         | _ ->
           fun value_expr ->
             let list_expr =
               expr_fns
               |> List.fold_left
                 (fun a efn ->
                    let e = efn value_expr in
                    [%expr [%e e]::[%e a]][@metaloc evhd.evhd_loc]
                 )
                 [%expr []][@metaloc evhd.evhd_loc]
             in
             [%expr BatEnum.concat (BatList.enum [%e list_expr])]
               [@metaloc evhd.evhd_loc]
    )
;;

let map_extension_holes_to_expressions
    (ops : continuation_operations)
    (source_fragment_uid : Fragment_uid.t)
    (cont_type_opt : core_type option)
    (cont_type_default : expression option)
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
           ops.co_expression
             exhd.exhd_loc
             source_fragment_uid
             target_fragment_uid
         in
         let extension_expr_opt =
           match snd exhd.exhd_extension with
           | PStr([]) -> None
           | PStr([{ pstr_desc = Pstr_eval(e, _); _}]) -> Some e
           | _ ->
             Some(
               error_as_expression exhd.exhd_loc @@
               "Unsupported non-expression payload in continuation extension"
             )
         in
         let cont_data_expr_opt =
           match cont_type_opt, extension_expr_opt with
           | None, None -> None
           | None, Some e ->
             Some(
               error_as_expression e.pexp_loc @@
               "Invalid continuation extension expression: no continuation " ^
               "data type given"
             )
           | Some t, None ->
             begin
               match cont_type_default with
               | Some e ->
                 Some([%expr ([%e e] : [%t t])][@metaloc exhd.exhd_loc])
               | None ->
                 Some(
                   error_as_expression exhd.exhd_loc @@
                   "Missing expression in continuation extension; either " ^
                   "provide an expression or declare a default."
                 )
             end
           | Some t, Some e ->
             Some([%expr ([%e e] : [%t t])][@metaloc exhd.exhd_loc])
         in
         let cont_result_payload =
           match cont_data_expr_opt with
           | None -> cont_expr
           | Some cont_data_expr ->
             [%expr ([%e cont_expr], [%e cont_data_expr])]
               [@metaloc exhd.exhd_loc]
         in
         [%expr
           BatEnum.singleton (Continuation_result [%e cont_result_payload])
         ][@metaloc exhd.exhd_loc]
    )
;;

let create_frag_fn_expr
    (loc : Location.t)
    (fragment_group : fragment_group)
    (ops : continuation_operations)
    (uid : Fragment_uid.t)
    (cont_type_opt : core_type option)
    (cont_default_opt : expression option)
  : expression =
  let fragment = Fragment_uid_map.find uid fragment_group.fg_graph in
  let vars = ops.co_pattern_variables uid in
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
  let frag_fn_pat = pattern_pseudo_tuple loc frag_fn_cont_patterns in
  let frag_fn_body =
    let eval_hole_fns =
      fragment.fragment_evaluation_holes
      |> map_evaluation_holes_to_functions ops uid
    in
    let ext_hole_exprs =
      fragment.fragment_extension_holes
      |> map_extension_holes_to_expressions
        ops uid cont_type_opt cont_default_opt
    in
    fragment.fragment_code (Some [%expr _input]) eval_hole_fns ext_hole_exprs
    |> process_nondeterminism_extensions
  in
  [%expr
    fun [%p frag_fn_pat] _input ->
      [%e frag_fn_body]
  ] [@metaloc loc]
;;

let create_frag_fn_decls
    (loc : Location.t)
    (fragment_group : fragment_group)
    (ops : continuation_operations)
    (cont_type_opt : core_type option)
    (cont_default_opt : expression option)
  : structure_item =
  let frag_fn_bindings =
    fragment_group.fg_graph
    |> Fragment_uid_map.keys
    |> Enum.filter
      (fun uid -> not @@ Fragment_uid.equal uid fragment_group.fg_entry)
    |> Enum.map
      (fun uid ->
         let expr =
           create_frag_fn_expr
             loc fragment_group ops uid cont_type_opt cont_default_opt
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
    (ops : continuation_operations)
    (start_fn_name : string)
    (function_of_body : expression -> expression)
    (cont_type_opt : core_type option)
    (cont_default_opt : expression option)
  : structure_item =
  let start_fragment_uid = fragment_group.fg_entry in
  let start_fragment =
    fragment_group.fg_graph
    |> Fragment_uid_map.find start_fragment_uid
  in
  let evaluation_hole_expression_functions =
    start_fragment.fragment_evaluation_holes
    |> map_evaluation_holes_to_functions ops start_fragment_uid
  in
  let extension_hole_expressions =
    start_fragment.fragment_extension_holes
    |> map_extension_holes_to_expressions
      ops start_fragment_uid cont_type_opt cont_default_opt

  in
  let start_fun_body =
    start_fragment.fragment_code
      None
      evaluation_hole_expression_functions
      extension_hole_expressions
    |> process_nondeterminism_extensions
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
    (cont_data_type : core_type option)
    (ops : continuation_operations)
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
         let cont_pat = ops.co_pattern loc uid in
         let vars = ops.co_pattern_variables uid in
         let vars_exprs =
           vars
           |> List.map
             (fun var ->
                { pexp_desc = Pexp_ident(mkloc var loc);
                  pexp_loc = loc;
                  pexp_attributes = [];
                }
             )
         in
         let case_call_arg = expression_pseudo_tuple loc vars_exprs in
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
  let continuation_result_type =
    match cont_data_type with
    | None -> [%type: 'unknown continuation_result]
    | Some t -> [%type: ('unknown,[%t t]) continuation_result]
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
                   [%t cont_type] ->
                 'input ->
                 [%t continuation_result_type] BatEnum.t)
              ][@metaloc loc];
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

(**
   Performs the continuation code transformation on the provided expression.
*)
let transform_expression (expr : expression) : fragment_group =
  let require_single_expression_payload ext =
    match snd ext with
    | PStr([{ pstr_desc = Pstr_eval(e, _); pstr_loc = _ }]) -> e
    | _ ->
      raise @@ Transformer.Transformation_failure(
        mkloc
          (Printf.sprintf "Extension %s requires single expression payload"
             (fst ext).txt)
          (fst ext).loc
      )
  in
  let require_single_let_expression_payload ext =
    let e = require_single_expression_payload ext in
    match e with
    | { pexp_desc = Pexp_let(recflag, [binding], body);
        pexp_loc = let_loc;
        pexp_attributes = let_attrs
      } ->
      (recflag, binding, body, let_loc, let_attrs)
    | _ ->
      raise @@ Transformer.Transformation_failure(
        mkloc
          (Printf.sprintf "Extension %s requires single let expression payload"
             (fst ext).txt)
          (fst ext).loc
      )
  in
  let rec extension_handler loc attrs ext =
    let open Transformer_monad in
    match (fst ext).txt with
    | "pop" ->
      Transformer.fragment_continuation extension_handler loc attrs ext
    | "pick"
    | "require"
    | "antirequire" ->
      (* Special handling is required for these extensions.  We need to add the
         extension to the fragment that the "let" binding winds up in, which may
         not be the entry fragment if the bindings are impure.  In both cases,
         the UID of the fragment containing the let will be the same as the UID
         of the body, so we can just manipulate the fragment at that UID.

         In particular, this is necessary to handle a case like
             let%require _ = [%pop] in ...
         because otherwise, the require annotation is placed on the new entry
         fragment rather than in the let binding.
      *)
      let (recflag, binding, body, let_loc, let_attrs) =
        require_single_let_expression_payload ext
      in
      let%bind body_group = Transformer.do_transform extension_handler body in
      let let_uid = body_group.fg_entry in
      let%bind bindings' =
        Transformer.do_transform_bindings extension_handler [binding]
      in
      let%bind let_group =
        Transformer.fragment_let let_loc let_attrs recflag bindings' body_group
      in
      (* Find the fragment which now contains the let binding that corresponds
         to the originally-annotated binding and wrap it in the extension. *)
      let frag = Fragment_uid_map.find let_uid let_group.fg_graph in
      let frag' =
        frag
        |> Fragment_utils.fragment_code_transform
          (fun code ->
             { pexp_desc =
                 Pexp_extension(
                   fst ext,
                   PStr([{ pstr_desc = Pstr_eval(code, []);
                           pstr_loc = loc;
                         }])
                 );
               pexp_loc = loc;
               pexp_attributes = attrs;
             }
          )
      in
      let let_group' =
        { let_group with
          fg_graph = Fragment_uid_map.add let_uid frag' let_group.fg_graph
        }
      in
      return let_group'
    | "pick_lazy" ->
      let e = require_single_expression_payload ext in
      let rec loop e' =
        match e' with
        | [%expr [%e? e1];[%e? e2]] -> e1 :: loop e2
        | _ -> [e']
      in
      let es = loop e in
      let%bind gs =
        es
        |> List.enum
        |> Enum.map (Transformer.do_transform extension_handler)
        |> sequence
        |> lift1 List.of_enum
      in
      Transformer.fragment_nondeterminism loc attrs gs
    | _ ->
      let e = require_single_expression_payload ext in
      let%bind g = Transformer.do_transform extension_handler e in
      Transformer.fragment_extension loc attrs (fst ext) (Some g)
  in
  expr
  |> Transformer.do_transform extension_handler
  |> Transformer_monad.run
    (Fragment_types.Fragment_uid.new_context ())
    (new_fresh_variable_context ())
;;

(* TODO:
   Provide support to statically distinguish between types of data for the first
   continuation which is reached (the type of the start function) and the
   remaining continuations (the type of the cont function).  A previous
   iteration of this existed before, but was replaced due to time constraints
   with the current less statically-checked support.  Implementing this properly
   would require knowing for a given fragment function which of the two types to
   use; the naive implementation wound up using the cont function type for
   fragments which were invoked by the start function due to a pick_lazy
   annotation.
*)

let generate_code_from_function
    ?continuation_type_name:(continuation_type_name = "continuation")
    ?start_fn_name:(start_fn_name = "start")
    ?cont_fn_name:(cont_fn_name = "cont")
    ?continuation_type_attributes:(continuation_type_attributes=[])
    ?continuation_data_type:(continuation_data_type = (None : core_type option))
    ?continuation_data_default:(continuation_data_default =
                                (None : expression option)
                               )
    (func_expr : expression)
  : structure =
  let func_expr' = rebind_parameters func_expr in
  let func_body, func_reconstruct = unroll_function func_expr' in
  let loc = func_expr.pexp_loc in
  let fragment_group = transform_expression func_body in
  let type_spec =
    create_continuation_type_spec loc continuation_type_name fragment_group
  in
  let ops = create_continuation_operations fragment_group type_spec in
  let type_decls =
    (* TODO: ppx_deriving attributes *)
    create_continuation_types type_spec
    |> List.map
      (fun type_decl ->
         let type_decl' =
           { type_decl with
             ptype_attributes =
               type_decl.ptype_attributes @ continuation_type_attributes
           }
         in
         { pstr_desc = Pstr_type(Recursive, [type_decl']);
           pstr_loc = loc;
         }
      )
  in
  let result_type_decl =
    let cr_typ =
      { ptyp_desc =
          Ptyp_constr(mkloc (Longident.Lident continuation_type_name) loc, []);
        ptyp_loc = loc;
        ptyp_attributes = [];
      }
    in
    match continuation_data_type with
    | None ->
      [%str
        type 'value continuation_result =
          | Value_result of 'value
          | Continuation_result of [%t cr_typ]
      ]
    | Some cd_typ ->
      [%str
        type 'value continuation_result =
          | Value_result of 'value
          | Continuation_result of [%t cr_typ] * [%t cd_typ]
      ]
  in
  let frag_fn_decls =
    create_frag_fn_decls
      loc fragment_group ops continuation_data_type continuation_data_default
  in
  let cont_fn_decl =
    create_cont_fn_decl
      loc
      fragment_group
      continuation_type_name
      cont_fn_name
      continuation_data_type
      ops
  in
  let start_fn_decl =
    create_start_fn_decl
      loc
      fragment_group
      ops
      start_fn_name
      func_reconstruct
      continuation_data_type
      continuation_data_default
  in
  type_decls @
  result_type_decl @
  [frag_fn_decls] @
  [start_fn_decl] @
  [cont_fn_decl]
;;
