(**
   A PDS programming module is broken into a series of continuations by the
   [Continuation_transform] module.  This module defines the form of those
   continuations as well as their relationships to each other.

   The overall result of a continuation transformation is a collection of
   continuations and a starting expression.  All of these code fragments will
   return a value TODO
*)

open Parsetree;;

type continuation =
  { cont_expr : expression;
    
  }
;;
