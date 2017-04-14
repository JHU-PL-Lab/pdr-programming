open Jhupllib;;

open Parsetree;;
open Asttypes;;
open Batteries;;
open Longident;;
open Ast_helper;;
open Ocaml_ast_utils;;

(*The context type is used to make sure each Cont (continuation), Goto,
  and variable created by the continuation transform function has a unique
  name. When a new Cont, Goto, or variable is created, the int stored in
  c_counter, g_counter, or v_counter, respectively, is used to create its
  name. That counter is then updated.*)

(*defines the context type*)
type context =
  {mutable c_counter: int;
   mutable g_counter: int;
   mutable v_counter: int}

(*initializes a context, with all counters starting at 0*)
let new_context () =
  { c_counter = 0;
    g_counter = 0;
    v_counter = 0;  }
;;

(*creates a new name of type Lident for a Cont and updates the corresponding
  counter of the given context. The name is of the form Part<int>.*)
let new_cont_name (c : context) =
  let n = c.c_counter in
  c.c_counter <- c.c_counter + 1;
  "Part" ^ string_of_int n
;;

(*creates a new name of type Lident for a Goto and updates the corresponding
  counter of the given context. The name is of the form Goto<int>.*)
let new_goto_name (c : context) =
  let n = c.g_counter in
  c.g_counter <- c.g_counter + 1;
  "Goto" ^ string_of_int n
;;

(*creates a new name of type string for a variable and updates the
  corresponding counter of the given context*)
let new_var_name (c : context) =
  let n = c.v_counter in
  c.v_counter <- c.v_counter + 1;
  "__varct__" ^ string_of_int n
;;

(*Handlers link code using Conts and Gotos. Each handler has the name of the
  Cont or Goto, stored as a pattern, the expresion associated with this Cont or
  Goto, and a handlertype, which indicates whether the handler is a Cont or a
  Goto. *)



(*used to indicate whether a handler is a Cont or a Goto. *)
type handlertype =
  | Cont_handler of string
  (** argument is name of continuation
  *)
  | Goto_handler of string * string option
  (** first argument is name of goto, second is name of variable
  *)
  [@@deriving eq, ord, show]
;;

(*The handler type contains the three parts of a handler: its name, the
  expression it is linked to, and its type (as indicated by a handlertype). *)
type handler =
  {
    h_exp : expression;
    h_type : handlertype;
  }
  [@@deriving eq, ord, show]
;;

module Handler_ord =
struct
  type t = handler
  let compare = compare_handler
end;;

module Handler_set =
  Set.Make (Handler_ord);;

(*A handler group is a collection of handlers arranged such that the back
  handler, which is needed when new handlers are added, is separate from the
  other handlers (if any), which are stored as a set in the others field.*)
type handler_group =
  { back : handler;
    others : Handler_set.t [@printer Pp_utils.pp_set pp_handler Handler_set.enum]
  }
  [@@deriving eq, show]
;;

(*Continuation transform returns an expression, which is the starting point,
  and a handler_group option, which contains all subsequent continuations. This
  will be None if and only if there are no continuations. *)
type continuation_transform_result = handler_group option * expression
  [@@deriving eq, show]
;;

(*Given a Longident.t, generates a constructor expression. Used when creating
  continuations in continuation_transform. *)
let constructor_exp (name : Longident.t) (inner : expression option) =
  {pexp_desc =
     Pexp_construct (locwrap name, inner);
   pexp_loc = !default_loc;
   pexp_attributes = []}
;;

(*Given a Longident.t, generates a constructor pattern. Used when creating
  continuations in continuation_transform. *)
let constructor_pat (name : Longident.t) (inner : pattern option) =
  {ppat_desc =
     Ppat_construct (locwrap name, inner);
   ppat_loc = !default_loc;
   ppat_attributes = []}
;;
(*Given an expression and a context, the contintuation transform function
  breaks the expression into pieces based on when a read is needed. Each piece
  contained in a handler, of type either Cont_handler or Goto_handler. The
  context c is used to name these handlers. The continuation transform function
  returns a pair of a handler group option containing all Gotos and Conts, and
  an expression acting as the "start" expression. *)
let rec continuation_transform
    (e : expression)
    (context : context)
  : handler_group option * expression =
  match e with
  | {pexp_desc = Pexp_ident _; _} -> (None, e)
  | {pexp_desc = Pexp_constant _; _} -> (None, e)
  | [%expr [%result [%e? r] ]] -> (None, [%expr Result [%e r]])
(*expression uses read extension; we need to create a new handler group and
  add a new handler to it. This new handler is a Continuation, with new_token
  (a variable name for the value read) as its expression. The name of the
  new handler becomes the start expression.*)
  | [%expr [%read]] ->
    let inner_cont_name = new_cont_name context in
    let next_token_exp = [%expr next_token] in (*the expression of the new handler*)
    let inner_cont_edesc = Pexp_construct (locwrap @@ Lident inner_cont_name, None) in
    let inner_cont_exp = {pexp_desc = inner_cont_edesc; pexp_loc = !default_loc; pexp_attributes = []} in
    let cont_edesc = Pexp_construct (locwrap (Lident "Part"), Some inner_cont_exp) in
    let cont_exp = {pexp_desc = cont_edesc; pexp_loc = !default_loc; pexp_attributes = []} in
    let h = {h_exp = next_token_exp; h_type = Cont_handler inner_cont_name} in
    let hgroup = Some {back = h; others = Handler_set.empty} in
    (hgroup, cont_exp)
(*expression is a let expression. TODO: finish this comment*)
  | {pexp_desc = Pexp_let (rflag, vblist, e2); _} ->
    (match rflag with
     | Recursive -> raise (Utils.Not_yet_implemented "Pexp_let recursive")
     | Nonrecursive ->
       (match vblist with
        | lh::[] ->
          let (hgroup1, e1') = continuation_transform lh.pvb_expr context in
          let (hgroup2, e2') = continuation_transform e2 context in
          (match hgroup1 with
           | None ->
             (hgroup2, [%expr let [%p lh.pvb_pat] = [%e e1'] in [%e e2']])
           | Some h1 ->
             let hback1 = h1.back in
             let hset1 = h1.others in
             (match hgroup2 with
              | None ->
                let new_back =
                  {hback1 with
                   h_exp = [%expr let [%p lh.pvb_pat] = [%e hback1.h_exp] in [%e e2']]} in
                let new_hgroup = Some {back = new_back; others = hset1} in
                (new_hgroup, e1')
              | Some h2 ->
                let new_hset =
                  let new_h_element =
                    {hback1 with
                     h_exp = [%expr let [%p lh.pvb_pat] = [%e hback1.h_exp] in [%e e2']]} in
                  Handler_set.union
                    (Handler_set.union (Handler_set.singleton new_h_element) hset1) h2.others in
                let new_hgroup = Some {back = h2.back; others = new_hset} in
                (new_hgroup, e1')
             )
          )
        | _ -> raise (Utils.Not_yet_implemented "Pexp_let nonrecursive multiple bindings")))
  | {pexp_desc = Pexp_function _; _} -> raise (Utils.Not_yet_implemented "Pexp_function") (*TODO*)
  | {pexp_desc = Pexp_fun _; _} -> raise (Utils.Not_yet_implemented "Pexp_fun") (*TODO*)
  | {pexp_desc = Pexp_apply _; _} -> (None, e)
  | {pexp_desc = Pexp_match (e0, case_list); _} ->
    (*currently throws an exception if any pattern has a guard*)
    let end_goto_name = new_goto_name context in
    let e_list =
      List.map (fun {pc_lhs = _; pc_guard = g_o; pc_rhs = e_i} ->
          (match g_o with
           | Some _ -> raise (Utils.Not_yet_implemented "Pexp_match with guard")
           | None -> continuation_transform e_i context)) case_list in
    let p_list =
      List.map (fun {pc_lhs = p_i; _} -> p_i) case_list in
    let set_producer (hgroup_i_o, e_i') =
      let goto_i_name = new_goto_name context in
      ((match hgroup_i_o with
       | None ->
         let h_i =
           {h_exp = constructor_exp (Lident "Goto") (Some (constructor_exp (Lident end_goto_name) (Some e_i')));
            h_type = Goto_handler (goto_i_name, None)} in
         Handler_set.singleton h_i
       | Some hgroup_i ->
         let h_i1 =
           {h_exp = e_i';
            h_type = Goto_handler (goto_i_name, None)} in
         let h_i2 =
           {h_exp = constructor_exp (Lident "Goto") (Some (constructor_exp (Lident end_goto_name) (Some hgroup_i.back.h_exp)));
            h_type = hgroup_i.back.h_type} in
         Handler_set.singleton h_i1
         |> Handler_set.add h_i2
         |> Handler_set.union hgroup_i.others), goto_i_name)
    in
    let sets_and_gotos_list = List.map set_producer e_list in
    let (all_sets, all_gotos) = List.split sets_and_gotos_list in
    let new_others = List.fold_left Handler_set.union Handler_set.empty all_sets in
    let v = new_var_name context in
    let v_exp = {pexp_desc = Pexp_ident (locwrap (Lident v));
                 pexp_loc = !default_loc;
                 pexp_attributes = []} in
    let new_back = {h_exp = v_exp;
                    h_type = Goto_handler (end_goto_name, Some v)} in
    let new_hgroup = Some {back = new_back; others = new_others} in
    let all_gotos_exp =
      List.map (fun s -> constructor_exp (Lident "Goto") (Some (constructor_exp s None))) (List.map (fun s -> Lident s) all_gotos) in
    let case_tuples = List.combine p_list all_gotos_exp in
    let case_maker (casepat, caseexp) =
      {pc_lhs = casepat; pc_guard = None; pc_rhs = caseexp} in
    let newcaselist = List.map case_maker case_tuples in
    let edesc = Pexp_match (e0, newcaselist) in
    let start = {pexp_desc = edesc; pexp_loc = !default_loc; pexp_attributes = []} in
    (new_hgroup, start)
  | {pexp_desc = Pexp_try (e0, case_list); _} -> (*TODO: refactor into Goto(Goto3) etc.*)
    let end_goto_name = new_goto_name context in
    let e_list =
      List.map (fun {pc_lhs = _; pc_guard = g_o; pc_rhs = e_i} ->
          (match g_o with
           | Some _ -> raise (Utils.Not_yet_implemented "Pexp_match with guard")
           | None -> continuation_transform e_i context)) case_list in
    let p_list =
      List.map (fun {pc_lhs = p_i; _} -> p_i) case_list in
    let set_producer (hgroup_i_o, e_i') =
      let goto_i_name = new_goto_name context in
      ((match hgroup_i_o with
          | None ->
            let h_i =
              {h_exp = constructor_exp (Lident "Goto") (Some (constructor_exp (Lident end_goto_name) (Some e_i')));
               h_type = Goto_handler (goto_i_name, None)} in
            Handler_set.singleton h_i
          | Some hgroup_i ->
            let h_i1 =
              {h_exp = e_i';
               h_type = Goto_handler (goto_i_name, None)} in
            let h_i2 =
              {h_exp = constructor_exp (Lident "Goto") (Some (constructor_exp (Lident end_goto_name) (Some hgroup_i.back.h_exp)));
               h_type = hgroup_i.back.h_type} in
            Handler_set.singleton h_i1
            |> Handler_set.add h_i2
            |> Handler_set.union hgroup_i.others), goto_i_name)
    in
    let sets_and_gotos_list = List.map set_producer e_list in
    let (all_sets, all_gotos) = List.split sets_and_gotos_list in
    let case_others = List.fold_left Handler_set.union Handler_set.empty all_sets in
    let v = new_var_name context in
    let v_exp = {pexp_desc = Pexp_ident (locwrap (Lident v));
                 pexp_loc = !default_loc;
                 pexp_attributes = []} in
    let new_back = {h_exp = v_exp;
                    h_type = Goto_handler (end_goto_name, Some v)} in
    let case_hgroup = {back = new_back; others = case_others} in
    let all_gotos_exp =
      List.map (fun s -> constructor_exp (Lident "Goto") (Some (constructor_exp s None))) (List.map (fun s -> Lident s) all_gotos) in
    let case_tuples = List.combine p_list all_gotos_exp in
    let case_maker (casepat, caseexp) =
      {pc_lhs = casepat; pc_guard = None; pc_rhs = caseexp} in
    let newcaselist = List.map case_maker case_tuples in
    (*let edesc = Pexp_try (e0, newcaselist) in
    let start = {pexp_desc = edesc; pexp_loc = !default_loc; pexp_attributes = []} in
      (new_hgroup, start)*)
    let (e_hgroup_o, e_start) = continuation_transform e0 context in
    (match e_hgroup_o with
     | None ->
       let edesc = Pexp_try (constructor_exp (Lident "Goto") (Some (constructor_exp (Lident end_goto_name) (Some e_start))), newcaselist) in
       let start = {pexp_desc = edesc; pexp_loc = !default_loc; pexp_attributes = []} in
       (Some case_hgroup, start)
     | Some e_hgroup ->
       let new_start_edesc = Pexp_try (e_start, newcaselist) in
       let start = {pexp_desc = new_start_edesc; pexp_loc = !default_loc; pexp_attributes = []} in
       let e_back = e_hgroup.back in
       let e_back_exp = e_back.h_exp in
       let new_e_back_exp = constructor_exp (Lident "Goto") (Some (constructor_exp (Lident end_goto_name) (Some e_back_exp))) in
       let new_e_back = {h_exp = new_e_back_exp;
                         h_type = e_back.h_type} in
       let try_map (c : case list) (h : handler) =
         (let new_desc = Pexp_try (h.h_exp, c) in
         let new_h_exp = {pexp_desc = new_desc;
                          pexp_loc = !default_loc;
                          pexp_attributes = []} in
         {h_exp = new_h_exp;
          h_type = h.h_type}) in
       let mapped_e_h_group_others = Handler_set.map (try_map newcaselist) e_hgroup.others in
       let mapped_e_back = try_map newcaselist new_e_back in
       let new_hgroup_others = (Handler_set.union mapped_e_h_group_others case_hgroup.others
                                |> Handler_set.union (Handler_set.singleton mapped_e_back)) in
       let new_hgroup = {back = case_hgroup.back;
                         others = new_hgroup_others} in
       (Some new_hgroup, start))
  | {pexp_desc = Pexp_tuple _; _} -> (None, e)
  | {pexp_desc = Pexp_construct _; _} -> (None, e)
  | {pexp_desc = Pexp_variant _; _} -> raise (Utils.Not_yet_implemented "Pexp_variant")
  | {pexp_desc = Pexp_record _; _} -> (None, e)
  | {pexp_desc = Pexp_field _; _} -> (None, e)
  | {pexp_desc = Pexp_setfield _; _} -> raise (Utils.Not_yet_implemented "Pexp_setfield")
  | {pexp_desc = Pexp_array _; _} -> raise (Utils.Not_yet_implemented "Pexp_array")
  | {pexp_desc = Pexp_ifthenelse (e1, e2, e3_o); _} ->
    let (hgroup2_o, e2') = continuation_transform e2 context in
    let e3 =
      (match e3_o with
       | Some e3 -> e3
       | None -> [%expr ()])
    in
    let (hgroup3_o, e3') = continuation_transform e3 context in
    (match (hgroup2_o, hgroup3_o) with
     | (None, None) ->  (None, [%expr if [%e e1] then [%e e2'] else [%e e3']])
     | (_, _) ->
       let goto2_name = new_goto_name context in
       let goto3_name = new_goto_name context in
       let goto4_name = new_goto_name context in
       let hgroup_others =
         (match (hgroup2_o, hgroup3_o) with
          | (None, None) -> Handler_set.empty
          | (Some hgroup2, None) -> hgroup2.others
          | (None, Some hgroup3) -> hgroup3.others
          | (Some hgroup2, Some hgroup3) -> Handler_set.union hgroup2.others hgroup3.others)
         |> Handler_set.union
           (match hgroup2_o with
            | Some hgroup2 ->
              Handler_set.union
                (Handler_set.singleton
                {h_exp = constructor_exp (Lident "Goto") (Some (constructor_exp (Lident goto4_name) (Some hgroup2.back.h_exp)));
                    h_type = hgroup2.back.h_type})
                (Handler_set.singleton
                   {h_exp = e2';
                    h_type = Goto_handler (goto2_name, None)})
            | None ->
              Handler_set.singleton
                {h_exp = constructor_exp (Lident "Goto") (Some (constructor_exp (Lident goto4_name) (Some e2')));
                 h_type = Goto_handler (goto2_name, None)})
         |> Handler_set.union
           (match hgroup3_o with
             | Some hgroup3 ->
               Handler_set.union
                 (Handler_set.singleton
                    {h_exp = constructor_exp (Lident "Goto") (Some (constructor_exp (Lident goto4_name) (Some hgroup3.back.h_exp)));
                     h_type = hgroup3.back.h_type})
                 (Handler_set.singleton
                    {h_exp = e3';
                     h_type = Goto_handler (goto3_name, None)})
             | None ->
               Handler_set.singleton
                 ({h_exp = constructor_exp (Lident "Goto") (Some (constructor_exp (Lident goto4_name) (Some e3')));
                   h_type = Goto_handler (goto3_name, None)}))
       in
       let hgroup_back =
         let x0_name = new_var_name context in
         {h_exp = {pexp_desc = Pexp_ident (locwrap (Lident x0_name));
                   pexp_loc = !default_loc;
                   pexp_attributes = []};
          h_type = Goto_handler (goto4_name, Some x0_name)}
       in
       let hgroup = Some {back = hgroup_back; others = hgroup_others} in
       let new_e = [%expr if [%e e1]
                          then [%e constructor_exp (Lident "Goto") (Some (constructor_exp (Lident goto2_name) None))]
                          else [%e constructor_exp (Lident "Goto") (Some (constructor_exp (Lident goto3_name) None))]] in
       (hgroup, new_e))
  | {pexp_desc = Pexp_sequence (e1, e2); _} ->
    let (hgroup1_o, e1') = continuation_transform e1 context in
    let (hgroup2_o, e2') = continuation_transform e2 context in
    (match (hgroup1_o, hgroup2_o) with
     | (None, None) ->
       let new_e = [%expr [%e e1']; [%e e2']] in
       (None, new_e)
     | (None, Some hgroup2) ->
       let new_e = [%expr [%e e1']; [%e e2']] in
       (Some hgroup2, new_e)
     | (Some hgroup1, None) ->
       let hback1_exp = hgroup1.back.h_exp in
       let new_hback_exp = [%expr [%e hback1_exp]; [%e e2']] in
       let new_hback = {h_exp = new_hback_exp;
                        h_type = hgroup1.back.h_type} in
       let new_hgroup = {back = new_hback;
                         others = hgroup1.others} in
       (Some new_hgroup, e1')
     | (Some hgroup1, Some hgroup2) ->
       let hgo1 = hgroup1.others in
       let hgb1_exp = hgroup1.back.h_exp in
       let hgb1_type = hgroup1.back.h_type in
       let hgo2 = hgroup2.others in
       let hgb2_back = hgroup2.back in
       let new_handler_exp = [%expr [%e hgb1_exp]; [%e e2']] in
       let new_handler = {h_exp = new_handler_exp;
                          h_type = hgb1_type} in
       let new_hgroup_others =
         Handler_set.union (Handler_set.add new_handler hgo1) hgo2 in
       let new_hgroup = {back = hgb2_back;
                         others = new_hgroup_others} in
       (Some new_hgroup, e1'))
  | {pexp_desc = Pexp_while _; _} -> raise (Utils.Not_yet_implemented "Pexp_while")
  | {pexp_desc = Pexp_for _; _} -> raise (Utils.Not_yet_implemented "Pexp_for")
  | {pexp_desc = Pexp_constraint _; _} -> raise (Utils.Not_yet_implemented "Pexp_constraint")
  | {pexp_desc = Pexp_coerce _; _} -> raise (Utils.Not_yet_implemented "Pexp_coerce")
  | {pexp_desc = Pexp_send _; _} -> raise (Utils.Not_yet_implemented "Pexp_send")
  | {pexp_desc = Pexp_new _; _} -> raise (Utils.Not_yet_implemented "Pexp_new")
  | {pexp_desc = Pexp_setinstvar _; _} -> raise (Utils.Not_yet_implemented "Pexp_setinstvar")
  | {pexp_desc = Pexp_override _; _} -> raise (Utils.Not_yet_implemented "Pexp_override")
  | {pexp_desc = Pexp_letmodule _; _} -> raise (Utils.Not_yet_implemented "Pexp_letmodule")
  | {pexp_desc = Pexp_assert _; _} -> raise (Utils.Not_yet_implemented "Pexp_assert")
  | {pexp_desc = Pexp_lazy _; _} -> raise (Utils.Not_yet_implemented "Pexp_lazy")
  | {pexp_desc = Pexp_poly _; _} -> raise (Utils.Not_yet_implemented "Pexp_poly")
  | {pexp_desc = Pexp_object _; _} -> raise (Utils.Not_yet_implemented "Pexp_object")
  | {pexp_desc = Pexp_newtype _; _} -> raise (Utils.Not_yet_implemented "Pexp_newtype")
  | {pexp_desc = Pexp_pack _; _} -> raise (Utils.Not_yet_implemented "Pexp_pack")
  | {pexp_desc = Pexp_open _; _} -> raise (Utils.Not_yet_implemented "Pexp_open")
  | {pexp_desc = Pexp_extension _; _}-> raise (Utils.Not_yet_implemented "Pexp_extension")
;;
