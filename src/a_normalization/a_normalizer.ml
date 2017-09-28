open Batteries;;
open Jhupllib;;

open Asttypes;;
open Parsetree;;

open Variable_utils;;

type a_normalization_context =
  { anc_fvc : fresh_variable_context
  }
;;

let new_a_normalization_context ?prefix:(prefix="__var_anorm") () =
  { anc_fvc = new_fresh_variable_context ?prefix:(Some prefix) () }
;;

(** A-translates a single OCaml expression. *)
let a_translate ?context:(context=None) (expr : expression) : expression =
  let context =
    match context with
    | None -> new_a_normalization_context ()
    | Some context -> context
  in
  (** Given an expression, replaces it with a simplified form.  If the
      expression is already simple (a constant or a variable), nothing occurs:
      the simple expression is simply returned together with the identity
      function.  Otherwise, a fresh variable is created and returned as a
      simple expression together with a function which will apply a let binding
      to define that variable to the original input expression. *)
  let simplify (e : expression) : expression * (expression -> expression) =
    match e.pexp_desc with
    | Pexp_ident _ -> (e, identity)
    | Pexp_constant _ -> (e, identity)
    | _ ->
      let loc = e.pexp_loc in
      let name = fresh_variable_name context.anc_fvc in
      let replacement =
        { pexp_loc = e.pexp_loc;
          pexp_desc = Pexp_ident { txt = Longident.Lident name; loc = loc };
          pexp_attributes = []
        }
      in
      let pattern =
        { ppat_desc = Ppat_var { txt = name; loc = loc };
          ppat_loc = loc;
          ppat_attributes = []
        }
      in
      (replacement, fun e' -> [%expr let [%p pattern] = [%e e] in [%e e']])
  in
  (** Let-binds a list as per simplify. *)
  let simplify_list (es : expression list) :
    expression list * (expression -> expression) =
    let es', wrappers = es |> List.map simplify |> List.split in
    (es',
     match wrappers with
     | [] -> identity
     | h::t -> List.fold_left (%) h t
    )
  in
  (** The primary A-translation function, defined here to capture the
      A-translation context. *)
  let rec atrans expr =
    match expr.pexp_desc with
    | Pexp_ident _ -> expr
    | Pexp_constant _ -> expr
    | Pexp_let (recursive_flag, variable_bindings, body_expression) ->
      begin
        match recursive_flag with
        | Recursive -> raise (Utils.Not_yet_implemented "Pexp_let (recursive)")
        | Nonrecursive ->
          let translated_variable_bindings =
            variable_bindings
            |> List.map
              (fun value_binding ->
                 { value_binding with
                   pvb_expr = atrans value_binding.pvb_expr })
          in
          let translated_body_expression = atrans body_expression in
          { expr with
            pexp_desc = Pexp_let (recursive_flag,
                                  translated_variable_bindings,
                                  translated_body_expression)
          }
      end
    | Pexp_function case_list ->
      let translated_case_list =
        case_list
        |> List.map
          (fun case ->
             { case with pc_rhs = atrans case.pc_rhs;
                         pc_guard = Option.map atrans case.pc_guard
             })
      in
      { expr with pexp_desc = Pexp_function translated_case_list }
    | Pexp_fun(arg_label, default_value, pattern, body) ->
      let translated_default_value = Option.map atrans default_value in
      let translated_body = atrans body in
      { expr with
        pexp_desc = Pexp_fun (arg_label,
                              translated_default_value,
                              pattern,
                              translated_body)
      }
    | Pexp_apply (func_expr, argument_list) ->
      let translated_func_expr, func_expr_wrap = simplify @@ atrans func_expr in
      let argument_labels, argument_exprs = List.split argument_list in
      let translated_argument_exprs = List.map atrans argument_exprs in
      let simplified_argument_exprs, argument_list_wrapper =
        simplify_list translated_argument_exprs
      in
      let translated_argument_list =
        List.combine argument_labels simplified_argument_exprs
      in
      func_expr_wrap @@ argument_list_wrapper @@
      { expr with
        pexp_desc = Pexp_apply(translated_func_expr, translated_argument_list)
      }
    | Pexp_match(subject_expr, case_list) ->
      let translated_subject_expr = atrans subject_expr in
      let translated_case_list =
        case_list
        |> List.map (fun case -> { case with
                                   pc_guard = Option.map atrans case.pc_guard;
                                   pc_rhs = atrans case.pc_rhs })
      in
      { expr with
        pexp_desc = Pexp_match(translated_subject_expr, translated_case_list)
      }
    | Pexp_try(try_expr, with_exprs) ->
      let translated_try_expr = atrans try_expr in
      let translated_with_exprs =
        with_exprs
        |> List.map (fun case -> { case with
                                   pc_guard = Option.map atrans case.pc_guard;
                                   pc_rhs = atrans case.pc_rhs })
      in
      { expr with
        pexp_desc = Pexp_try(translated_try_expr, translated_with_exprs)
      }
    | Pexp_tuple element_exprs ->
      let translated_exprs = List.map atrans element_exprs in
      let simplified_exprs, wrapper = simplify_list translated_exprs in
      wrapper @@
      { expr with
        pexp_desc = Pexp_tuple simplified_exprs
      }
    | Pexp_construct(constructor_name, body_option) ->
      begin
        match body_option with
        | None -> expr
        | Some body ->
          let translated_body = atrans body in
          let simplified_body, wrapper = simplify translated_body in
          wrapper @@
          { expr with
            pexp_desc = Pexp_construct(constructor_name, Some simplified_body)
          }
      end
    | Pexp_variant(label, body_option) ->
      begin
        match body_option with
        | None -> expr
        | Some body ->
          let translated_body = atrans body in
          let simplified_body, wrapper = simplify translated_body in
          wrapper @@
          { expr with
            pexp_desc = Pexp_variant(label, Some simplified_body)
          }
      end
    | Pexp_record(term_list, with_clause_prefix) ->
      let translated_with_clause_prefix =
        Option.map atrans with_clause_prefix
      in
      let term_labels, term_exprs = List.split term_list in
      let translated_term_exprs = List.map atrans term_exprs in
      let simplified_term_exprs, term_expr_wrapper =
        simplify_list translated_term_exprs
      in
      let simplified_term_list =
        List.combine term_labels simplified_term_exprs
      in
      let simplified_with_clause_prefix, with_clause_prefix_wrapper =
        match translated_with_clause_prefix with
        | None -> (None, identity)
        | Some prefix ->
          let simplified_prefix, wrap = simplify prefix in
          (Some simplified_prefix, wrap)
      in
      term_expr_wrapper @@
      with_clause_prefix_wrapper @@
      { expr with
        pexp_desc = Pexp_record(simplified_term_list,
                                simplified_with_clause_prefix)
      }
    | Pexp_field(body, label) ->
      let translated_body = atrans body in
      let simplified_body, wrapper = simplify translated_body in
      wrapper @@
      { expr with
        pexp_desc = Pexp_field(simplified_body, label)
      }
    | Pexp_setfield _ -> raise (Utils.Not_yet_implemented "Pexp_setfield")
    | Pexp_array _ -> raise (Utils.Not_yet_implemented "Pexp_array")
    | Pexp_ifthenelse(condition_expr, then_expr, else_expr_option) ->
      let translated_condition_expr = atrans condition_expr in
      let simplified_condition_expr, condition_wrapper =
        simplify translated_condition_expr
      in
      condition_wrapper @@
      { expr with
        pexp_desc = Pexp_ifthenelse(
            simplified_condition_expr,
            atrans then_expr,
            Option.map atrans else_expr_option)
      }
    | Pexp_sequence(e1,e2) ->
      { expr with
        pexp_desc = Pexp_sequence(atrans e1, atrans e2)
      }
    | Pexp_while _ -> raise (Utils.Not_yet_implemented "Pexp_while")
    | Pexp_for _ -> raise (Utils.Not_yet_implemented "Pexp_for")
    | Pexp_constraint _ -> raise (Utils.Not_yet_implemented "Pexp_constraint")
    | Pexp_coerce _ -> raise (Utils.Not_yet_implemented "Pexp_coerce")
    | Pexp_send _ -> raise (Utils.Not_yet_implemented "Pexp_send")
    | Pexp_new _ -> raise (Utils.Not_yet_implemented "Pexp_new")
    | Pexp_setinstvar _ -> raise (Utils.Not_yet_implemented "Pexp_setinstvar")
    | Pexp_override _ -> raise (Utils.Not_yet_implemented "Pexp_override")
    | Pexp_letmodule _ -> raise (Utils.Not_yet_implemented "Pexp_letmodule")
    | Pexp_letexception _ -> raise (Utils.Not_yet_implemented "Pexp_letexception")
    | Pexp_assert _ -> raise (Utils.Not_yet_implemented "Pexp_assert")
    | Pexp_lazy _ -> raise (Utils.Not_yet_implemented "Pexp_lazy")
    | Pexp_poly _ -> raise (Utils.Not_yet_implemented "Pexp_poly")
    | Pexp_object _ -> raise (Utils.Not_yet_implemented "Pexp_object")
    | Pexp_newtype _ -> raise (Utils.Not_yet_implemented "Pexp_newtype")
    | Pexp_pack _ -> raise (Utils.Not_yet_implemented "Pexp_pack")
    | Pexp_open _ -> raise (Utils.Not_yet_implemented "Pexp_open")
    | Pexp_extension _ -> expr
    | Pexp_unreachable -> expr
  in
  atrans expr
;;
