(**
   This module defines an A-translation routine for OCaml ASTs.  Specifically,
   it defines a routine which, given an OCaml AST, produces an observationally
   equivalent OCaml AST which has only simple expressions (constants or
   variables) in all non-control-flow expressions.  For instance, the bodies of
   all tuple expressions, constructor expressions, and record expressions will
   be simple variables (with their contents evaluated in an appropriate order by
   hoisted let expressions).  The bodies of conditional expressions and match
   expressions, for instance, will be recursively A-normalized but otherwise
   unaffected (in order to preserve control flow).  The bodies of let
   expressions are similarly A-normalized but otherwise unaffected in order to
   preserve variable scope.
*)

open Parsetree;;

(** A type representing contextual information about A-normalization.  If
    multiple ASTs are A-normalized using the same context, they are guaranteed
    to be compatible (in that they can appear in the same AST without causing
    A-normalization-inspired problems). *)
type a_normalization_context

(** Creates a fresh A-normalization context. *)
val new_a_normalization_context :
  ?prefix:string -> unit -> a_normalization_context

(** Performs A-normalization of an OCaml AST.  If no A-normalization context
    is provided, a fresh context is created and used. *)
val a_translate :
  ?context:(a_normalization_context option) -> expression -> expression
