open Jhupllib;;

open Pdr_programming_continuation_extensions.Fragment_types;;

let string_of_ident i =
  match i with
  | Longident.Lident s -> s
  | _ -> raise @@ Utils.Invariant_failure "Don't know how to convert this!"
;;

let int_of_uid uid =
  int_of_string @@ Fragment_uid.show uid
;;
