open Parsetree;;

open Pdr_programming_utils.Variable_utils;;

open Fragment_types;;

type extension_predicate = extension -> bool

type context =
  {
    fragment_context : Fragment_uid.context;
    (** Used to generate fragment UIDs. *)

    fresh_variable_context : fresh_variable_context;
    (** Used to generate fresh variables. *)

    continuation_extension : extension_predicate;
    (** Determines whether an extension represents a point of continuation
        within the program. *)

    homomorphic_extension : extension_predicate;
    (** Determines whether an extension is homomorphic to transformation.  If
        so, its payload will be converted homomorphically; otherwise, conversion
        ignores the extension and its payload. *)
  }
;;

module Base = struct
  type 'a m = context -> 'a
  let return (x : 'a) : 'a m = fun _ -> x
  let bind (x : 'a m) (f : 'a -> 'b m) : 'b m =
    fun context -> f (x context) context
end;;

module Utils = Jhupllib_monad_utils.Make(Base);;

include Monad.Make(Base);;
let mapM = Utils.mapM;;
let sequence = Utils.sequence;;

let run
    (fragment_context : Fragment_uid.context)
    (fresh_variable_context : fresh_variable_context)
    (continuation_extension : extension -> bool)
    (homomorphic_extension : extension -> bool)
    (x : 'a m)
  : 'a =
  x { fragment_context = fragment_context;
      fresh_variable_context = fresh_variable_context;
      continuation_extension = continuation_extension;
      homomorphic_extension = homomorphic_extension;
    }
;;

let get_fragment_uid_context () : Fragment_uid.context m =
  fun (context : context) -> context.fragment_context
;;

let get_fresh_variable_context () : fresh_variable_context m =
  fun (context : context) -> context.fresh_variable_context
;;

let get_continuation_predicate () : extension_predicate m =
  fun (context : context) -> context.continuation_extension
;;

let get_homomorphism_predicate () : extension_predicate m =
  fun (context : context) -> context.homomorphic_extension
;;

let fresh_uid () : Fragment_uid.t m =
  let%bind context = get_fragment_uid_context () in
  return @@ Fragment_uid.fresh ~context:context ()
;;

let fresh_var () : string m =
  let%bind context = get_fresh_variable_context () in
  return @@ fresh_variable_name context
;;

let is_continuation_extension (ext : extension) : bool m =
  get_continuation_predicate () <*> return ext
;;

let is_homomorphic_extension (ext : extension) : bool m =
  get_homomorphism_predicate () <*> return ext
;;
