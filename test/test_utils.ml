open Jhupllib;;

open Pdr_programming_continuation_extensions;;
open Pdr_programming_utils.Variable_utils;;

open Fragment_types;;

let string_of_ident i =
  match i with
  | Longident.Lident s -> s
  | _ -> raise @@ Utils.Invariant_failure "Don't know how to convert this!"
;;

let int_of_uid uid =
  int_of_string @@ Fragment_uid.show uid
;;

let test_transform_code expr =
  expr
  |> Transformer.do_transform
    (let rec extension_handler loc attrs ext =
       match (fst ext).Location.txt with
       | "pop" ->
         Transformer.fragment_extension_continuation loc attrs ext
       | "pick"
       | "require" ->
         Transformer.fragment_extension_homomorphism
           extension_handler loc attrs ext
       | "pick_lazy" ->
         Transformer.fragment_extension_nondeterminism
           extension_handler loc attrs ext
       | _ ->
         Transformer.fragment_extension_noop loc attrs ext
     in extension_handler)
  |> Transformer_monad.run
    (Fragment_uid.new_context ())
    (new_fresh_variable_context ~prefix:"var" ())
;;
