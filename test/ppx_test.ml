open Batteries;;
type t = A | B | C of int;;
module%continuation Foo = struct
  [%%start_function_name "start"];;
  [%%continue_function_name "cont"];;
  [%%continuation_data_type: int];;
  [%%continuation_data_default 0];;
  let%continuation_fn foo (a : int) =
    ();
    let%pick (z : t) = List.enum [A;B;C 1;C 2] in
    let%require C (y : int) = z in
    let _ = [%pop 4] in
    [%pick_lazy
      begin
        let%require B = let _ = [%pop] in B in
        (a,y)
      end;
      begin
        (y,a)
      end;
      begin
        let%antirequire 0 = 0 in (0,0)
      end;
    ]
  ;;
end
;;
