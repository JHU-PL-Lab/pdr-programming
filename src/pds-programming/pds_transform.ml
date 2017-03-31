open Batteries;;
open Continuation_transform;;
open Parsetree;;
open Ast_helper;;

let dynamic_pop_function_generator 
    (hg : handler_group)
  : expression =
  let others_list = Handler_set.elements hg.others in
  let handlers_list = (hg.back)::others_list in
  let part_filter (h : handler) =
    (
      if h.h_type == Cont_handler then
        true
      else
        false
    ) in
  let cont_list = List.filter part_filter handlers_list in
  let handler_to_pat_and_expr_pair (h : handler) = (h.h_pat, h.h_exp) in
  let pat_and_expr_list = List.map handler_to_pat_and_expr_pair cont_list in
  let pattern_unwrap (p : pattern * expression) =
    (
      let (pat, exp) = p in
      let unwrapped_pat =
        (
          match pat.ppat_desc with
          | Ppat_construct (_, inner_pat_o) ->
            (
              match inner_pat_o with
              | Some inner_pat -> inner_pat
              | None -> failwith "unexpected handler"
            )
          | _ -> failwith "unexpected handler"
        ) in
      (unwrapped_pat, [%expr execute_task [%e exp]])
    ) in
  let unwrapped_pat_and_exp_list = List.map pattern_unwrap pat_and_expr_list in
  let case_map (p : pattern * expression) =
    (
      let (pat, exp) = p in
      {
        pc_lhs = pat;
        pc_guard = None;
        pc_rhs = exp
      }
    ) in
  let case_list = List.map case_map unwrapped_pat_and_exp_list in
  let desc = Pexp_match ([%expr dtp], case_list) in
  {
    pexp_desc = desc;
    pexp_loc = !default_loc;
    pexp_attributes = []
  }
;;
