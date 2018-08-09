(**
   This module contains support utilities for metaprograms that need to create
   variants with large numbers of constructors.  OCaml places a hard limit of
   246 non-nullary constructors per variant.  This module mitigates this issue
   by automatically generating wrapper variant types.

   That is, we'll have:

     type foo = Wrapper1_000 of foo_0 | Wrapper1_200 of foo_1 | ...
     type foo_0 = C000 of ... | C001 of ... | ...
     type foo_1 = C200 of ... | C201 of ... | ...

   If necessary, we can even wrap further (foo_0_0, etc.).

   Given the index of a constructor and the largest index of any constructor, we
   can compute the position in the tree of wrappers that the constructor would
   take.  For instance, constructor number 12,500 in a set of 50,000
   constructors would be called something like
       Wrapper2_00000(Wrapper1_12400(C12500(...)))
   Here, the outermost type (say, "foo") would have two constructors:
   Wrapper2_00000 (ranging over the first 40,000 constructors) and
   Wrapper2_40000 (randing over the last 10,000 constructors).  The single
   argument to Wrapper2_00000 would be an element of a type (say, "foo_0")
   which itself would contain 200 constructors: Wrapper1_00000, Wrapper1_00200,
   Wrapper1_00400, and so on.  Each of these constructors would take a single
   argument of a similar type (say, "foo_0_0" for Wrapper1_00000, "foo_0_1" for
   Wrapper1_00200, and so on).  These types would contain the actual
   constructors for the continuations.
*)

open Parsetree;;

type big_variant_spec;;

(**
   Creates a specification for a "big variant".  This is a data structure which
   can be used to create type definitions for a series of wrapper variant types
   as well as to generate expressions which construct those wrappers and
   patterns which match them.

   The wrapper prefix function accepts two arguments -- the integer index of the
   level of the wrapper and a string indicating the zero-padded index of a
   variant constructor -- and generates an appropriate wrapper constructor name.
*)
val create_big_variant :
    ?constructors_per_level:int ->
    ?wrapper_constructor_name_fn:(int -> string -> string) ->
    string ->
    constructor_declaration list ->
    big_variant_spec
;;

(**
   Creates the type declarations for the variant type and its dedicated wrapper
   types.  These declarations effectively encode the big variant type in OCaml.
*)
val create_big_variant_types :
  Location.t -> big_variant_spec -> type_declaration list
;;

(**
   Creates an expression which creates an value of a big variant's type.  This
   expression may actually create a series of nested variant values to
   circumvent the OCaml compiler limit.
*)
val construct_big_variant :
  Location.t -> big_variant_spec -> int -> expression list -> expression
;;

(**
   Creates a pattern which will destruct a value of a big variant's type.  This
   pattern may actually contain a series of patterns, each of which destructs
   a distinct wrapper in the value.
*)
val destruct_big_variant :
  Location.t -> big_variant_spec -> int -> pattern list -> pattern
;;
