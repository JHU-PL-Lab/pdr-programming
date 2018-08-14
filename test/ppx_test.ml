module Foo = struct
  let%transition foo (a : int) =
    let x = [%pop] in
    (a,x)
  ;;
end
;;
