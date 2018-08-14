open Migrate_parsetree;;
open OCaml_406.Ast;;
open Ast_mapper;;
open Asttypes;;
open Parsetree;;

open Pdr_programming_generation;;

let transform_structure_item mapper structure_item : structure =
  (* We need to run last; all of the PPX extensions inside of this structure
     item should be processed before we try to mess with control flow. *)
  let structure_item' = default_mapper.structure_item mapper structure_item in
  match structure_item'.pstr_desc with
  | Pstr_extension(({txt = "transition"; loc = _}, PStr(body)), _) ->
    begin
      match body with
      | [ { pstr_desc = Pstr_value(_, [binding]); pstr_loc = _; } ] ->
        Continuation_code.generate_code_from_function binding.pvb_expr
      | _ ->
        raise @@ Location.Error(
          Location.error
            ~loc:structure_item.pstr_loc @@
          "transition extension must be applied to a single let binding")
    end
  | _ -> [structure_item]
;;

let mapper =
  { default_mapper with
    structure =
      fun mapper s ->
        s
        |> List.map (transform_structure_item mapper)
        |> List.concat
  }
;;
