open Batteries;;
open Continuation_transform;;
open Parsetree;;
open Ast_helper;;
open Longident;;

(*generates the body of the function taking a dtp and a pop*)
let dynamic_pop_function_generator
    (hg : handler_group)
  : expression =
  let others_list = Handler_set.elements hg.others in
  let handlers_list = (hg.back)::others_list in
  let part_filter (h : handler) =
    (
      match h.h_type with
      | Cont_handler _ -> true
      | Goto_handler _ -> false
    ) in
  let cont_list = List.filter part_filter handlers_list in
  let handler_to_type_and_expr_pair (h : handler) = (h.h_type, h.h_exp) in
  let type_and_expr_list = List.map handler_to_type_and_expr_pair cont_list in
  let type_to_pattern (t : handlertype * expression) =
    (
      let (htype, hexp) = t in
      let hpat =
        (match htype with
        | Cont_handler s ->
          constructor_pat (Lident s) None
        | Goto_handler (s, _) -> failwith "unexpected handler")
      in
      (hpat, [%expr execute_task [%e hexp]])
    ) in
  let pat_and_exp_list = List.map type_to_pattern type_and_expr_list in
  let case_map (p : pattern * expression) =
    (
      let (pat, exp) = p in
      {
        pc_lhs = pat;
        pc_guard = None;
        pc_rhs = exp
      }
    ) in
  let case_list = List.map case_map pat_and_exp_list in
  let desc = Pexp_match ([%expr dtp], case_list) in
  {
    pexp_desc = desc;
    pexp_loc = !default_loc;
    pexp_attributes = []
  }
;;

(*generates the body of a function taking a Goto that will be called continue_function*)
let goto_function_generator
    (hg: handler_group)
  : expression =
  let others_list = Handler_set.elements hg.others in
  let handlers_list = (hg.back)::others_list in
  let goto_filter (h : handler) =
    (
      match h.h_type with
      | Cont_handler _ -> false
      | Goto_handler _ -> true
    ) in
  let goto_list = List.filter goto_filter handlers_list in
  let handler_to_type_and_expr_pair (h : handler) = (h.h_type, h.h_exp) in
  let type_and_expr_list = List.map handler_to_type_and_expr_pair goto_list in
  let type_to_pattern (t : handlertype * expression) =
    (
      let (htype, hexp) = t in
      let hpat =
        (match htype with
         | Cont_handler _ -> failwith "unexpected handler"
         | Goto_handler (s, s_o) ->
           (
             match s_o with
             | Some str ->
               constructor_pat (Lident s) (Some (constructor_pat (Lident str) None))
             | None -> constructor_pat (Lident s) None
           ))
      in
      (hpat, [%expr execute_task [%e hexp]])
    ) in
  let pat_and_exp_list = List.map type_to_pattern type_and_expr_list in
  let case_map (p : pattern * expression) =
    (
      let (pat, exp) = p in
      {
        pc_lhs = pat;
        pc_guard = None;
        pc_rhs = exp
      }
    ) in
  let case_list = List.map case_map pat_and_exp_list in
  let desc = Pexp_match ([%expr dtp], case_list) in
  {
    pexp_desc = desc;
    pexp_loc = !default_loc;
    pexp_attributes = []
  }
;;

(*generates the body of a function that begins the processing of the continuation transform output.
  needs to take an initial state as input. initial_function is the function that takes
  the continuation transform start expression and produces another task.*)
let engine_generator _ =
  [%expr execute_task (initial_function state)]
;;

(*generates the body of the initial function. must take a state and will return a task*)
let initial_function_generator (e: expression) =
  e
;;

(*generates the body of the recursive function that processes the tasks.
  the function generated must take a task as input. must be mutually recursive with
  function handling dynamic pops*)
let execute_task_generator _ =
  [%expr match task with
       | Part p -> Enum.singleton (Dynamic_terminus(p), [])
       | Goto g -> execute_task (continue_function g)
       | Result (state, actions) -> Enum.singleton (Static_terminus(state), actions)]
;;
