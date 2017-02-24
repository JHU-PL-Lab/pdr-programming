open Continuation_transform;;
open Jhupllib_pp_utils;;
open Ocaml_ast_utils;;

let () =
  let expr =
    [%expr
      match state with
      | Number n ->
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
  let hgo,e = continuation_transform expr @@ new_context () in
  begin
    match hgo with
    | None -> print_endline "<no handler group>"
    | Some hg -> print_endline @@ show_handler_group hg
  end;
  print_endline @@ pp_to_string Pprintast.expression e
;;
