open Batteries;;
type t = A | B | C of int;;
module Foo = struct
  let%transition foo (a : int) =
    let%pick (z : t) = List.enum [A;B;C 1;C 2] in
    let%require C (y : int) = z in
    let _ = [%pop] in
    [%pick_lazy
      (a,y);
      (y,a)
    ]
  ;;
end
;;
