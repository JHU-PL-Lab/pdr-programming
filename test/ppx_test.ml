open Batteries;;
type t = A | B | C of int;;
module%continuation Foo = struct
  [%%start_function_name "start"];;
  [%%continue_function_name "cont"];;
  [%%continuation_type_name "continuation"];;
  [%%continuation_type_attributes][@@deriving eq, ord, show, to_yojson];;
  [%%continuation_data_type: int];;
  let%continuation_fn foo (a : int) =
    let (x : int) = (fun x -> x) 4 in
    let _ = [%pop 1] in
    let (y : int) = x + 1 in
    let _ = [%pop 2] in
    (a,x,y)
  ;;
end
;;
(* module%continuation Foo = struct
  [%%start_function_name "start"];;
  [%%continuation_data_type: int];;
  [%%continue_function_name "cont"];;
  [%%continuation_data_default 0];;
  let%continuation_fn foo (a : int) =
    ();
    let%pick (z : t) = List.enum [A;B;C 1;C 2] in
    let%require C (y : int) = z in
    [%pop 4];
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
;; *)
