open Batteries;;
open Continuation_transform;;
open Parsetree;;
open Ast_helper;;
open Asttypes;;
open Ocaml_ast_utils;;
open Longident;;

(*generates the body of the function taking a dtp and a pop*)
(*this is handle_udp called something different; look at old unit tests to see Dph modules*)
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
(*body of initial edge function; include in module Dph*)
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
(*include in module Dph; define first*)
let execute_task_generator _ =
  [%expr match task with
       | Part p -> Enum.singleton (Dynamic_terminus(p), [])
       | Goto g -> execute_task (continue_function g)
       | Result (state, actions) -> Enum.singleton (Static_terminus(state), actions)]
;;

(*module generator*)

let check_payload (p : payload) : structure_item =
  match p with
  | PStr payload_structure ->
    (
      match payload_structure with
      | payload_item::[] ->
        (
          match payload_item.pstr_desc with
          | Pstr_type _ -> payload_item
          | _ -> failwith "extension payload must be type declaration"
        )
      | _ -> failwith "extension must only contain exactly one type declaration"
    )
  | _ -> failwith "extension payload must be type declaration"
;;

let rec unwrap_state (s : structure) : structure_item =
  match s with
  | first::rest ->
    (
      match first.pstr_desc with
      | Pstr_extension (ext, _)->
        (
          let (s_loc, p) = ext in
          match s_loc.txt with
          | "state" -> check_payload p
          | _ -> unwrap_state rest
        )
      | _ -> unwrap_state rest
    )
  | [] -> failwith "no state declaration"
;;

let rec unwrap_stack_elt (s : structure) : structure_item =
  match s with
  | first::rest ->
    (
      match first.pstr_desc with
      | Pstr_extension (ext, _)->
        (
          let (s_loc, p) = ext in
          match s_loc.txt with
          | "stack_element" -> check_payload p
          | _ -> unwrap_state rest
        )
      | _ -> unwrap_state rest
    )
  | [] -> failwith "no stack element declaration"
;;

let user_decls_module_generator (mb : module_binding) : structure_item =
  match mb.pmb_expr.pmod_desc with
  | Pmod_structure s ->
    let state_structure_item = unwrap_state s in
    let stack_elt_structure_item = unwrap_stack_elt s in
    let (new_structure : structure) = [state_structure_item; stack_elt_structure_item] in
    let mod_desc = Pmod_structure new_structure in
    let new_module = {
      pmod_desc = mod_desc;
      pmod_loc = !default_loc;
      pmod_attributes = [];
    } in
    let new_module_binding =
      {
        pmb_name = locwrap "UserDecls";
        pmb_expr = new_module;
        pmb_attributes = [];
        pmb_loc = !default_loc;
      } in
    let structure_desc = Pstr_module new_module_binding in
    {
      pstr_desc = structure_desc;
      pstr_loc = !default_loc;
    }
  | _ -> failwith "TODO"
;;

let user_decls_open_generator _ : structure_item =
  [%stri
    open UserDecls;;
  ]
;;

let keep_structure_item (s : structure_item) : bool =
  match s.pstr_desc with
  | Pstr_extension (ext, attr) ->
    let (s_loc, p) = ext in
    (match s_loc.txt with
    | "state" -> false
    | "stack_element" -> false
    | "transition" -> false
    | _ -> true)
  | _ -> true
;;

let other_user_decls_generator (mb : module_binding) : structure_item list =
  match mb.pmb_expr.pmod_desc with
  | Pmod_structure s ->
    let (s_list : structure_item list) = s in
    List.filter keep_structure_item s_list
  | _ -> failwith "TODO"
;;

let basis_module_generator _ : structure_item =
  [%stri
    module Basis =
    struct
      type state = UserDecls.state;;
      type stack_element = UserDecls.stack_element;;
    end;;
  ]
;;

let dph_module_generator (mb : module_binding) : structure_item =
  failwith "TODO"
;;

let create_new_user_module (s_list : structure_item list) (s : string loc) : toplevel_phrase =
  failwith "TODO"
;;

(*TODO: if the user writes declarations, we should keep them in the same order if possible*)

let module_generator (top : toplevel_phrase) : toplevel_phrase = (*TODO: take and return structure instead*)
  let user_structure =
    (
      match top with
      | Ptop_def s -> s
      | Ptop_dir _ -> failwith "not a module!"
    )
  in
  match user_structure with
  | user_module::[] ->
    (
      match user_module.pstr_desc with
      | Pstr_module mb ->
        let user_decls_module = user_decls_module_generator mb in
        let user_decls_open = user_decls_open_generator () in
        let other_user_decls = other_user_decls_generator mb in
        (*TODO: put declarations in right order (to preserve dependencies)*)
        let basis_module = basis_module_generator () in
        let dph_module = dph_module_generator mb in
        let structure_list = user_decls_module::user_decls_open::basis_module::dph_module::other_user_decls in
        create_new_user_module structure_list (mb.pmb_name)
      | _ -> failwith "not a module"
    )
  | _ -> failwith "need exactly one module defined by user"
;;
