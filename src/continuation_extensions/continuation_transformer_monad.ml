open Continuation_fragment_types;;
open Parsetree;;
open Variable_utils;;

type extension_predicate = extension -> bool

type context =
  { fragment_context : Fragment_uid.context;
    fresh_variable_context : fresh_variable_context;
    extension_predicate : extension_predicate
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
    (predicate : extension -> bool)
    (x : 'a m)
  : 'a =
  x { fragment_context = fragment_context;
      fresh_variable_context = fresh_variable_context;
      extension_predicate = predicate }
;;

let get_fragment_uid_context () : Fragment_uid.context m =
  fun (context : context) -> context.fragment_context
;;

let get_fresh_variable_context () : fresh_variable_context m =
  fun (context : context) -> context.fresh_variable_context
;;

let get_predicate () : extension_predicate m =
  fun (context : context) -> context.extension_predicate
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
  get_predicate () <*> return ext
;;
