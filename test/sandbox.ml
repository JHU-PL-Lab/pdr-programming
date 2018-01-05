open Batteries;;
open Jhupllib;;

open Asttypes;;
open Continuation_fragment_types;;
open Parsetree;;
open Printf;;

let debug_render_fragment (f : fragment) : string =
  let input_expr_opt =
    match f.fragment_input_hole with
    | None -> None
    | Some _ -> Some ([%expr _INPUT])
  in
  let eval_hole_fns =
    f.fragment_evaluation_holes
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
  in
  let ext_hole_exprs =
    f.fragment_extension_holes
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
  in
  let e = f.fragment_code input_expr_opt eval_hole_fns ext_hole_exprs in
  let expr_str = Pprintast.string_of_expression e in
  sprintf "===== #%s =====\n%s" (Fragment_uid.show f.fragment_uid) expr_str
;;

let debug_render_fragment_group (g : fragment_group) : string =
  let entry_string = sprintf "Entry: %s" (Fragment_uid.show g.fg_entry) in
  let exit_string =
    sprintf "Exits: %s"
      (Pp_utils.pp_to_string Fragment_uid_set.pp g.fg_exits) in
  let fragments_string =
    Fragment_uid_map.values g.fg_graph
    |> Enum.fold
      (fun s f ->
         s ^ (if s = "" then "" else "\n") ^ debug_render_fragment f
      ) ""
  in
  sprintf "%s\n%s\n%s" entry_string exit_string fragments_string
;;

let main () =
  if Array.length Sys.argv != 2 then begin
    prerr_endline "Expected exactly one argument.";
    Pervasives.exit 1
  end;
  let source = Sys.argv.(1) in
  let lexbuf = Lexing.from_string source in
  let ast = Parse.expression lexbuf in
  ast
  |> Continuation_transformer.do_transform
  |> Continuation_transformer_monad.run
    (Continuation_fragment_types.Fragment_uid.new_context ())
    (fun (name,payload) ->
       name.txt = "pop"
    )
  |> debug_render_fragment_group
  |> print_endline
;;

main ();;
