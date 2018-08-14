open Batteries;;
type t = A | B | C of int;;
module Foo = struct
  let%transition foo (a : int) =
    let%pick (z : t) = List.enum [A;B;C 1;C 2] in
    let%require C (y : int) = z in
    let x = [%pop] in
    (a,x,y)
  ;;
end
;;
