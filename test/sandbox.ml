(* open Batteries;; *)
(* open Jhupllib;; *)

(* open Asttypes;; *)
(* open Parsetree;; *)

(* open Pdr_programming_continuation_extensions;; *)
open Pdr_programming_generation;;
(* open Pdr_programming_utils;; *)

(* open Sandbox_crud;; *)

let main () =
  let expr =
    [%expr
      fun (a : int) ->
        let%pick (z : t) = List.enum [A;B;C 1;C 2] in
        let%require C (y : int) = z in
        let b = 4 in
        let _ = [%pop] in
        [%pick_lazy
          begin
            let%require B = let _ = [%pop] in B in
            (a,y,b)
          end;
          begin
            (y,a,b)
          end;
        ]
    ]
  in
  Continuation_code.generate_code_from_function expr
;;

main ();;
