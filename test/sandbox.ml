open Continuation_transform;;
open Jhupllib_pp_utils;;
open Ocaml_ast_utils;;
open Ocaml_a_translator;;

let () =
  let expr =
    [%expr
      match state with
      | Number n ->
        if n = 1 then
          [%result (Count(0), [])]
        else
          let dividing_primes = foo n in
          let p = dividing_primes in
          [%result Number(n/p), [Prime]]
      | Count n ->
        begin
          match [%read] with
          | Bottom -> [%result Count(n), []]
          | Prime -> [%result Count(n+1), []]
        end
    ]
  in
  let a_expr = a_translator expr @@ Ocaml_a_translator.new_context () in
  let hgo,e = continuation_transform a_expr @@ Continuation_transform.new_context () in
  begin
    match hgo with
    | None -> print_endline "<no handler group>"
    | Some hg ->
      let dynamic_pop_function_body = dynamic_pop_generator hg in
      print_endline @@ pp_to_string Pprintast.expression dynamic_pop_function_body
  end;
  print_endline @@ pp_to_string Pprintast.expression e
;;
