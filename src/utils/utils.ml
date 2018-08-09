open Batteries;;

let pad_string n c s =
  if String.length s < n then
    String.make (n - String.length s) c ^ s
  else
    s
;;
