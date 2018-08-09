(**
   This module defines a data structure and associated routines representing
   variant types modeling continuations.  Given a fragment group, this module
   can create type declarations for continuation values within that fragment and
   can generate construction and destruction code for those variants by fragment
   UID.
*)

open Parsetree;;

open Pdr_programming_continuation_extensions.Fragment_types;;

type continuation_type_spec;;

val create_continuation_type_spec :
  Location.t -> string -> fragment_group -> continuation_type_spec
;;

val create_continuation_types :
  continuation_type_spec -> type_declaration list
;;

val construct_continuation_value :
  Location.t -> continuation_type_spec -> Fragment_uid.t -> expression list ->
  expression
;;

val destruct_continuation_value :
  Location.t -> continuation_type_spec -> Fragment_uid.t -> pattern list ->
  pattern
;;
