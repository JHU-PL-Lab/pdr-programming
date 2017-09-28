(**
   This module defines general utility functions for variables.
*)

type fresh_variable_context

(** Creates a new context for generating fresh variables. *)
val new_fresh_variable_context :
  ?prefix:string -> unit -> fresh_variable_context

val fresh_variable_name : fresh_variable_context -> string
