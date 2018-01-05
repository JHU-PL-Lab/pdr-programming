(**
   This module defines general utility functions for variables.
*)

open Batteries;;
open Jhupllib;;
open Parsetree;;

type fresh_variable_context

(** Creates a new context for generating fresh variables. *)
val new_fresh_variable_context :
  ?prefix:string -> unit -> fresh_variable_context

val fresh_variable_name : fresh_variable_context -> string

module Var_set :
sig
  include Set.S with type elt = Longident.t
  val pp : t Pp_utils.pretty_printer
  val unions : t list -> t
end;;

module Var_map :
sig
  include Map.S with type key = Longident.t
  val pp : 'a Pp_utils.pretty_printer -> 'a t Pp_utils.pretty_printer
  val disjoint_union : 'a t -> 'a t -> 'a t
  val disjoint_unions : 'a t list -> 'a t
  val union_left : 'a t -> 'a t -> 'a t
end;;

(** Determines the variables bound by a given OCaml pattern. *)
val bound_pattern_vars : pattern -> Var_set.t

(** Determines the variables bound by a given OCaml pattern. *)
val bound_pattern_vars_with_type : pattern -> core_type option Var_map.t

(** Determines the free variables in an OCaml AST. *)
val free_expr_vars : expression -> Var_set.t
