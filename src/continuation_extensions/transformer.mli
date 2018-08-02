open Parsetree;;

open Fragment_types;;
open Transformer_monad;;

(**
   This module provides a tool for transforming an OCaml AST into a collection
   of fragments based upon the appearance of specific extensions in the original
   tree.  Given a recognizer for those extensions, the fragments produced by
   this tool will be parts of the computation which do not include those
   extensions.  The extensions themselves are replaced by metadata which
   connects fragments, indicating which fragment is to be executed after which
   other fragment.

   This tool is useful for processing extensions that define non-deterministic
   or concurrent control-flow behavior which require considerable structural
   transformation to encode.  The extensions are used to describe the points at
   which standard evaluation is insufficient.  Often, the use of a monad would
   be preferrable to this transformation as the transformation requires a larger
   amount of information to be fixed at compile time.  In some cases -- such as
   storing the non-deterministic continuations in a set or other non-duplicated
   data structure -- the OCaml runtime is incapable of representing the
   computation as a monad and this transformer becomes appropriate.
*)

val do_transform : expression -> fragment_group m;;
