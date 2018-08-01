open Batteries;;
open Jhupllib;;

open Parsetree;;
open Pdr_programming_utils.Variable_utils;;

(* TODO: clean up the documentation here *)

(*
Alrighty... here we go again.

* Our objective is to transform an expression with extensions into a fragment
  graph.  After this transformation is complete, we imagine a process termed
  "stitching" which will reassemble the fragments into code which implements the
  continuation-based semantics we have in mind.
* A fragment is a single unit of code which can run independently of the
  continuation extensions we are processing.  That is, a fragment is "pure"
  code.
  * To facilitate the stitching of fragments into an implementation of the
    continuation semantics, this "pure" code cannot just be an AST; it should be
    a nearly-complete AST suspended in construction (implemented as a function).
    * Each fragment carries a unique ID.
    * A fragment may require an optional input subexpression.  This is the
      result of a previously-executed subexpression in the original source (in
      cases such as "let x = [%pop] in ...") which is handled by impure
      semantics.
    * A fragment has one or more output points.  Each output point is either an
      evaluation point or an extension point.
      * Extension points are caused by appearances of appropriate extensions in
        the original expression (such as "let x = [%pop] in ...").  In this
        case, the fragment preceeding that step will include an extension point
        for the [%pop].
      * Evaluation points are caused by merges in control flow after the
        original expression is fragmented.  For instance, the expression
        "let x = if b then 4 else [%pop] in ..." causes an evaluation point for
        the then clause which will lead to the same fragment that the [%pop]
        eventually does.
      * Each output point is associated with the ID of the fragment to which it
        leads.  If this ID is not specified, then the output point represents a
        result of the original expression.
      * During stitching, each evaluation point is matched with a function of
        type (expr->expr).  The input expression is the code which produces the
        value generated at this point by the original expression.  The function
        permits the stitching code to modify the returned value (by e.g.
        wrapping it).
      * During stitching, each extension point is replaced by an expression
        which correctly implements the behavior of the continuation extension
        that triggered it.
    * Each output point in a fragment should record which variables it can
      provide (and what their types are).  In stitching, this will be used to
      pass to the next fragment the bound variables that it needs.
    * Each fragment retains the set of variables which are free in its body.
      Further, these variables may be associated with the UID of the fragment
      which will bind them.  If a free variable is not associated with a
      fragment UID, then it is free in the entire expression in which it
      appears.  If a free variable is associated with a UID, then its value will
      be supplied by the fragment with that UID.
* A fragment graph is a collection of these fragments.  Edges are defined by the
  IDs stored in output points, so no explicit edges are necessary in the
  fragment graph structure.
* A fragment group contains a graph as well as some summary metadata.  This
  includes:
    * The entry fragment for the group.  Every group has an entry fragment even
      if the fragment doesn't have an input hole.
    * The exit fragments for the group.  Every group has at least one exit
      fragment: the last part of the code that will run.  Branching control flow
      expressions (such as if-then-else) may have multiple exit fragments.  This
      is relevant when those control flows must be merged.
* With the above data types, the goal is to write a function which transforms
  expressions into fragment graphs.  Even simple, constant functions produce
  whole graphs; the job of the function is produce the least fragmented graphs
  possible.
*)

(** A module defining fragment UIDs. *)
module Fragment_uid: Uids.Uid_module;;

(** The metadata describing an input hole. *)
type input_hole_data =
  {
    inhd_loc: Location.t
    (** The location describing the point at which the input for this fragment
        was created. *)
  }
;;

(** The metadata describing an output hole. *)
type evaluation_hole_data =
  { evhd_loc: Location.t;
    (** The location describing the origin of the expression that produced the
          evaluated value. *)

    evhd_target_fragment: Fragment_uid.t option;
    (** The ID of the fragment which should be evaluated after this one, or
        [None] to indicate that the evaluated result of this evaluation hole is
        the result of the overall expression. *)

    evhd_bound_variables: core_type option Var_map.t;
    (** The variables which are bound by the point that this evaluation hole is
        reached and their corresponding types (if known). *)
  }
;;

(** The metadata describing an action hole. *)
type extension_hole_data =
  { exhd_loc: Location.t;
    (** The location describing the extension that created the hole. *)

    exhd_extension: extension;
    (** The extension which caused the creation of this action hole. *)

    exhd_target_fragment: Fragment_uid.t option;
    (** The ID of the fragment to which this hole leads, or [None] to indicate
        that the value generated by the extension (which would be passed to the
        next fragment) is the result of the overall expression. *)

    exhd_bound_variables: core_type option Var_map.t;
    (** The variables which are bound by the point that this extension hole is
        reached and their corresponding types (if known). *)
  }
;;

(** The type of a code fragment. *)
type fragment =
  { fragment_uid: Fragment_uid.t;
    (** The UID of this fragment. *)

    fragment_loc: Location.t;
    (** A location to attribute to this fragment. *)

    fragment_free_variables: Var_set.t;
    (** The set of variables which are free in this fragment. *)

    fragment_externally_bound_variables:
      (Fragment_uid.t * core_type option) Var_map.t;
    (** The set of variables in this fragment which are bound by other fragments
        in its group.  The pair identifies the UID of the fragment which binds
        the variable for this fragment as well as the variable's type, if it is
        known. *)

    fragment_input_hole: input_hole_data option;
    (** The input hole for this fragment (if one exists). *)

    fragment_evaluation_holes: evaluation_hole_data list;
    (** The evaluation holes for this fragment. *)

    fragment_extension_holes: extension_hole_data list;
    (** The extension holes for this fragment. *)

    fragment_code :
      expression option ->
      (expression -> expression) list ->
      expression list ->
      expression;
    (** A function representing the fragment's code with a number of holes in
        it.  The arguments provide a means to fill the input, evaluation, and
        extension holes, in that order.  Input holes are filled using a single
        expression (representing the value of the previous fragment).    Evaluation holes are filled using a function from the simple expression
        describing the result of this fragment (e.g. a variable) onto the
        expression which should be used in its place; this gives the supplier
        the opportunity to wrap the result in some meaningful call or
        constructor.  Extension holes are filled using a single expression which
        will result in the desired extension-specific behavior. *)
  }
;;

(** The type of a fragment UID set. *)
module Fragment_uid_set : sig
  include Set.S with type elt = Fragment_uid.t;;
  val pp : t Pp_utils.pretty_printer
end;;
(** The type of a fragment UID dictionary. *)
module Fragment_uid_map : Map.S with type key = Fragment_uid.t;;

type fragment_group =
  { fg_graph : fragment Fragment_uid_map.t;
    fg_loc : Location.t;
    fg_entry : Fragment_uid.t;
    fg_exits : Fragment_uid_set.t
  }
;;
