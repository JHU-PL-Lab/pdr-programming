open Batteries;;

let%transition foo (a : int) =
  let%pick (n : int) = List.enum [1;2;3] in
  let x = [%pop] in
  (n,a,x)
;;
