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

type extension_handler =
  Location.t -> attributes -> extension -> fragment_group m
;;

val sequentialize_fragment_groups :
  Location.t -> fragment_group list -> (expression list -> expression) ->
  fragment_group m
;;

val fragment_ident :
  Location.t -> attributes -> Longident.t Asttypes.loc -> fragment_group m
;;

val fragment_constant :
  Location.t -> attributes -> constant -> fragment_group m
;;

val fragment_let :
  Location.t -> attributes -> Asttypes.rec_flag ->
  (pattern * fragment_group * attributes * Location.t) list ->
  fragment_group ->
  fragment_group m
;;

val fragment_apply :
  Location.t -> attributes -> fragment_group ->
  (Asttypes.arg_label * fragment_group) list ->
  fragment_group m
;;

val fragment_match :
  Location.t -> attributes -> fragment_group ->
  (pattern * fragment_group option * fragment_group) list ->
  fragment_group m
;;

val fragment_tuple :
  Location.t -> attributes -> fragment_group list -> fragment_group m
;;

val fragment_construct :
  Location.t -> attributes -> Longident.t Asttypes.loc ->
  fragment_group option ->
  fragment_group m
;;

val fragment_ifthenelse :
  Location.t -> attributes ->
  fragment_group -> fragment_group -> fragment_group ->
  fragment_group m
;;

val fragment_constraint :
  Location.t -> attributes -> fragment_group -> core_type -> fragment_group m
;;

val fragment_extension :
  Location.t -> attributes -> string Asttypes.loc -> fragment_group option ->
  fragment_group m
;;

val fragment_continuation :
  Location.t -> attributes -> string Asttypes.loc -> fragment_group m
;;

val fragment_nondeterminism :
  Location.t -> attributes -> fragment_group list -> fragment_group m
;;

val do_transform : extension_handler -> expression -> fragment_group m;;

val do_transform_bindings :
  extension_handler -> value_binding list ->
  (pattern * fragment_group * attributes * Warnings.loc) list m
;;
