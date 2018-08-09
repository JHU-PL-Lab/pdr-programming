(** This module contains data types and routines pertaining to data flow within
    a given fragment group.  After a fragment group is constructed, these
    routines generate a data structure which describes how data moves from
    fragment to fragment during execution.  While some amount of this is
    addressed during fragment construction, variable shadowing presents a
    particular difficulty.  For instance, consider the following code:

        let a = 4 in
        let x = [%pop] in
        let y =
          let a = 2 in
          let z = [%pop] in
          a
        in
        a

    This code will break into four fragments which are executed in order:

        let a = 4 in EXT_HOLE 1   (* fragment 0 *)

        let x = INPUT_HOLE in     (* fragment 1 *)
        let a = 2 in EXT_HOLE 2

        let z = INPUT_HOLE in     (* fragment 2 *)
        EVAL_HOLE(3, a)

        let y = INPUT_HOLE in a   (* fragment 3 *)

    Continuations must transfer data from each fragment to the next.  The
    externally-bound variable map for framgent 2 will indicate that its x
    variable is bound by fragment 1.  Importantly, the externally-bound variable
    map for fragment 3 will indicate that its x variable is bound by fragment 0.
    As a consequence, we must carry *two* x variables from fragment 1 to
    fragment 2.  In general, the continuation of fragment 2 may require an
    arbitrary number of variables, all named x.  At most one of those variables
    is intended for fragment 2; the rest must be passed along to future
    fragments.

    The data flow analysis in this module determines from a fragment group which
    continuations must carry intermediary values which are not used in the
    target fragment but are necessary to carry along to future fragments.
*)

open Batteries;;
open Jhupllib;;

open Pdr_programming_continuation_extensions.Fragment_types;;
open Pdr_programming_utils.Variable_utils;;

type intermediate_var = Longident_value.t * Fragment_uid.t;;

module Intermediate_var : sig
  type t = intermediate_var;;
  val equal : t -> t -> bool;;
  val compare : t -> t -> int;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
end;;
;;

module Intermediate_var_set : sig
  include Set.S with type elt = intermediate_var;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
end;;

(**
   Determines which intermediate variables are necessary for each fragment in a
   fragment group.  An intermediate variable is one which must be passed through
   a fragment but which is not used by a fragment.  In the example in the module
   comment, for instance, fragments 1 and 2 have variable x from fragment 0 as
   an intermediate variable.  Neither fragment 0 nor fragment 3 has any
   intermediate variables.

   If a fragment both uses a variable and relays it to another fragment, then
   that variable is considered intermediate (as well as externally bound).  For
   example, the following code creates three fragments:

       let a = 5 in         (* fragment 0 *)
       let x = [%pop] in
       let b = a in         (* fragment 1 *)
       let y = [%pop] in
       a                    (* fragment 2 *)

   In this case, both fragment 1 and fragment 2 have variable a externally bound
   by fragment 0.  Because a path exists from fragment 0 to fragment 2 through
   fragment 1, a is also an intermediate variable for fragment 1: that variable
   must be passed along to fragment 2.
*)
val determine_intermediates :
  fragment_group -> Intermediate_var_set.t Fragment_uid_map.t
