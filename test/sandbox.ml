open Batteries;;
open Jhupllib;;

open Asttypes;;

open Pdr_programming_continuation_extensions;;
open Pdr_programming_utils;;

let main () =
  let expr = [%expr
    match a with
    | Foo ->
      let x = 4 in
      let y = [%pop] in
      x
  ]
  in
  let result =
    expr
    |> Transformer.do_transform
    |> Transformer_monad.run
      (Fragment_types.Fragment_uid.new_context ())
      (Variable_utils.new_fresh_variable_context ~prefix:"var" ())
      (fun (name,_) -> name.txt = "pop")
  in
  print_endline @@ Pp_utils.pp_to_string Fragment_pp.pp_fragment_group result
;;

main ();;
