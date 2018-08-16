open Batteries;;

open Migrate_parsetree;;
open OCaml_406.Ast;;
open Ast_mapper;;
open Asttypes;;
open Parsetree;;

open Pdr_programming_generation;;
open Pdr_programming_utils.Ast_utils;;
open Pdr_programming_utils.Utils;;

type continuation_conversion_configuration =
  { ccc_continuation_data_type : core_type option;
    ccc_start_function_name : string;
    ccc_continue_function_name : string;
  }
;;

type parse_result =
  | Inert_extension
  | Configuration_change of (continuation_conversion_configuration ->
                             continuation_conversion_configuration)
  | Parse_error of string
;;

let parse_continuation_configuration_extension (ext : extension)
  : parse_result =
  let config_string ext string_fn =
    match snd ext with
    | PStr([
        { pstr_desc =
            Pstr_eval(
              { pexp_desc = Pexp_constant(Pconst_string ((s : string), _));
                _ },
              _
            );
          _;
        }
      ]) ->
      string_fn s
    | _ ->
      Parse_error(Printf.sprintf "%s payload must be a string constant"
                    (fst ext).txt)
  in
  match (fst ext).txt with
  | "continuation_data_type" ->
    begin
      match snd ext with
      | PTyp(core_type) ->
        Configuration_change(
          fun config -> { config with
                          ccc_continuation_data_type = Some core_type
                        }
        )
      | _ ->
        Parse_error("continuation_data_type payload must be a type")
    end
  | "start_function_name" ->
    config_string ext
      (fun s ->
         Configuration_change(
           fun config -> { config with
                           ccc_start_function_name = s
                         }
         )
      )
  | "continue_function_name" ->
    config_string ext
      (fun s ->
         Configuration_change(
           fun config -> { config with
                           ccc_continue_function_name = s
                         }
         )
      )
  | _ ->
    Inert_extension
;;

let convert_continuation_structure
    (module_loc : Location.t) (structure : structure)
  : structure =
  (*
    We need to gather up the contents of the module.  There should be exactly
    one function declaration which is annotated with "continuation".  There may
    also be some extensions which represent configuration options.
  *)
  let default_configuration =
    { ccc_continuation_data_type = None;
      ccc_start_function_name = "start";
      ccc_continue_function_name = "cont";
    }
  in
  (* Scan for options. *)
  let nonoption_items, config_changes =
    structure
    |> List.map
      (fun (structure_item : structure_item) ->
         match structure_item.pstr_desc with
         | Pstr_extension(ext, _) ->
           begin
             match parse_continuation_configuration_extension ext with
             | Inert_extension -> ([structure_item], identity)
             | Configuration_change f -> ([], f)
             | Parse_error(errmsg) ->
               ([structure_item;
                 error_as_structure_item structure_item.pstr_loc errmsg
                ],
                identity
               )
           end
         | _ ->
           ([structure_item], identity)
      )
    |> List.split
    |> first List.concat
  in
  let configuration =
    List.fold_left (fun a e -> e a) default_configuration config_changes
  in
  (* Perform transformation.  Doing this as a fold so that, if any extra
     continuation functions exist, they can be converted into error nodes.
  *)
  let result_structure, saw_continuation =
    nonoption_items
    |> List.fold_left
      (fun (collected_structure, seen_continuation_yet) item ->
         match item with
         | { pstr_desc =
               Pstr_extension(({ txt = "continuation_fn"; _ }, payload), _);
             _
           } ->
           if seen_continuation_yet then
             let err =
               error_as_structure_item item.pstr_loc @@
               "continuation module must no more than one continuation function"
             in
             (err :: collected_structure, true)
           else
             begin
               match payload with
               | PStr([{ pstr_desc = Pstr_value(recflag, [binding]);
                         pstr_loc = str_loc
                       }]) ->
                 if recflag <> Nonrecursive then
                   let err =
                     error_as_structure_item str_loc
                       "\"continuation_fn\" function must be non-recursive"
                   in
                   (err :: collected_structure, true)
                 else
                   (* TODO: make use of type configuration here *)
                   let continuation_structure =
                     Continuation_code.generate_code_from_function
                       ~start_fn_name:configuration.ccc_start_function_name
                       ~cont_fn_name:configuration.ccc_continue_function_name
                       binding.pvb_expr
                   in
                   (* This is silly, but we're assembling the list of structure
                      items backwards and they get flipped back at the end.  So
                      we need to attach the new continuation structure in
                      reverse so that the later reversal will make it correct.
                   *)
                   ((List.rev continuation_structure) @ collected_structure,
                    true)
               | PStr _ ->
                 let err =
                   error_as_structure_item item.pstr_loc @@
                   "\"continuation_fn\" extension payload must be exactly " ^
                   "one let-binding for a function"
                 in
                 (err :: collected_structure, seen_continuation_yet)
               | _ ->
                 let err =
                   error_as_structure_item item.pstr_loc @@
                   "\"continuation_fn\" extension payload must be exactly " ^
                   "one let-binding for a function"
                 in
                 (err :: collected_structure, seen_continuation_yet)
             end
         | _ ->
           (item::collected_structure, seen_continuation_yet)
      )
      ([], false)
    |> first List.rev
  in
  let errs =
    if not saw_continuation then
      [ error_as_structure_item module_loc @@
        "\"continuation\" module must have exactly one function let-binding " ^
        "annotated with \"continuation_fn\""
      ]
    else
      []
  in
  result_structure @ errs
;;

let continuation_transform_structure_item mapper structure_item
  : structure_item =
  (* We need to run last; all of the PPX extensions inside of this structure
     item should be processed before we try to mess with control flow. *)
  let structure_item' = default_mapper.structure_item mapper structure_item in
  match structure_item'.pstr_desc with
  | Pstr_extension(({txt = "continuation"; loc = _}, PStr(body)), _) ->
    begin
      match body with
      | [ { pstr_desc =
              Pstr_module(
                { pmb_expr =
                    { pmod_desc = Pmod_structure(module_structure);
                      _
                    } as cont_module_expr;
                  _
                } as cont_module_binding
              );
            pstr_loc = _;
          } as cont_module
        ] ->
        let converted_structure =
          convert_continuation_structure cont_module.pstr_loc module_structure
        in
        let new_module =
          { cont_module with
            pstr_desc = Pstr_module(
                { cont_module_binding with
                  pmb_expr = { cont_module_expr with
                               pmod_desc = Pmod_structure(converted_structure);
                             };
                }
              );
          }
        in
        print_endline @@ Jhupllib.Pp_utils.pp_to_string Pprintast.structure
          [new_module];
        new_module;
      | _ ->
        error_as_structure_item structure_item'.pstr_loc @@
        "\"continuation\" extension must be applied to a single module " ^
        "structure"
    end
  | _ -> structure_item'
;;

let mapper =
  { default_mapper with
    structure_item = continuation_transform_structure_item
  }
;;
