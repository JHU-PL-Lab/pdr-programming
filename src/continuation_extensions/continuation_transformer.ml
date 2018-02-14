open Batteries;;
open Jhupllib;;

open A_normalizer;;
open Asttypes;;
open Continuation_fragment_constructors;;
open Continuation_fragment_types;;
open Continuation_transformer_monad;;
open Parsetree;;
open Variable_utils;;

(* FIXME:
   The current state of the below code is a mess and shouldn't really be used.
   Here's what probably needs to happen next.

   We want to be able to write a nice and simple recursive tree traversal to
   produce the appropriate output data structure.  The current form -- fragment
   list -- is unsurprisingly insufficient.  It's also unfortunately not enough
   for the fragments to have lists of holes; they should be described as
   dictionaries mapping from some new kind of UID onto the appropriate data.
   Once we have this, we can define the correct output type as some kind of
   fragment graph.

   Charlotte's model was top-down: the "handler groups" (equivalent to fragment
   graphs here) kept track of their "back" so they could be extended.  Here,
   let's try a bottom-up approach.  The fragment graph can distinguish its
   entry fragment -- the one with no input hole -- and we can build on that.
   The base case of construction would be the base cases of the tree (e.g.
   variables, constants, etc.) and combinators should allow us to manipulate
   the entry point appropriately (e.g. by modifying its fragment_code function
   to wrap the output in something else).  It should almost never be necessary
   to manipulate any part of a fragment graph other than its entry point.

   None of this takes into account how free variables are handled, but that's a
   different matter entirely.  It's clear that the free variables must flow from
   top to bottom, but that doesn't stop us from actually consuming the data in
   a bottom-up fashion.
*)

(* TODO: main function: a-normalize, transform, etc. *)

let rec do_transform (e : expression)
  : fragment_group m =
  let loc = e.pexp_loc in
  let attrs = e.pexp_attributes in
  match e.pexp_desc with
  | Parsetree.Pexp_ident x ->
    fragment_ident loc attrs x
  | Parsetree.Pexp_constant c ->
    fragment_constant loc attrs c
  | Parsetree.Pexp_let(rec_flag,bindings,body) ->
    let%bind bindings' =
      bindings
      |> List.enum
      |> mapM
        (fun binding ->
           let%bind bind_expr = do_transform binding.pvb_expr in
           return
             (binding.pvb_pat,
              bind_expr,
              binding.pvb_attributes,
              binding.pvb_loc)
        )
      |> lift1 List.of_enum
    in
    let%bind body' = do_transform body in
    fragment_let loc attrs rec_flag bindings' body'
  | Parsetree.Pexp_function _ ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_function")
  | Parsetree.Pexp_fun(_,_,_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_fun")
  | Parsetree.Pexp_apply(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_apply")
  | Parsetree.Pexp_match(e,cases) ->
    let%bind g = do_transform e in
    let%bind fcases =
      lift1 List.of_enum @@ mapM do_transform_case @@ List.enum cases
    in
    fragment_match loc attrs g fcases
  | Parsetree.Pexp_try(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_try")
  | Parsetree.Pexp_tuple(es) ->
    let%bind gs = mapM do_transform @@ List.enum es in
    fragment_tuple loc attrs @@ List.of_enum gs
  | Parsetree.Pexp_construct(name,eo) ->
    let%bind go =
      match eo with
      | Some e -> lift1 Option.some @@ do_transform e
      | None -> return None
    in
    fragment_construct loc attrs name go
  | Parsetree.Pexp_variant(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_variant")
  | Parsetree.Pexp_record(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_record")
  | Parsetree.Pexp_field(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_field")
  | Parsetree.Pexp_setfield(_,_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_setfield")
  | Parsetree.Pexp_array _ ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_array")
  | Parsetree.Pexp_ifthenelse(e1,e2,e3o) ->
    let e3 = Option.default_delayed (fun () -> [%expr ()]) e3o in
    let%bind g1 = do_transform e1 in
    let%bind g2 = do_transform e2 in
    let%bind g3 = do_transform e3 in
    fragment_ifthenelse loc attrs g1 g2 g3
  | Parsetree.Pexp_sequence(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_sequence")
  | Parsetree.Pexp_while(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_while")
  | Parsetree.Pexp_for(_,_,_,_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_for")
  | Parsetree.Pexp_constraint(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_constraint")
  | Parsetree.Pexp_coerce(_,_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_coerce")
  | Parsetree.Pexp_send(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_send")
  | Parsetree.Pexp_new _ ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_new")
  | Parsetree.Pexp_setinstvar(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_setinstvar")
  | Parsetree.Pexp_override _ ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_override")
  | Parsetree.Pexp_letmodule(_,_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_letmodule")
  | Parsetree.Pexp_letexception(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_letexception")
  | Parsetree.Pexp_assert _ ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_assert")
  | Parsetree.Pexp_lazy _ ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_lazy")
  | Parsetree.Pexp_poly(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_poly")
  | Parsetree.Pexp_object _ ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_object")
  | Parsetree.Pexp_newtype(_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_newtype")
  | Parsetree.Pexp_pack _ ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_pack")
  | Parsetree.Pexp_open(_,_,_) ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_open")
  | Parsetree.Pexp_extension ext ->
    fragment_extension loc attrs ext
  | Parsetree.Pexp_unreachable  ->
    raise @@ Utils.Not_yet_implemented("transform: Pexp_unreachable")

and do_transform_case (c : case)
  : (pattern * fragment_group option * fragment_group) m =
  let%bind guard_opt =
    match c.pc_guard with
    | None -> return None
    | Some guard_expr -> Option.some <$> do_transform guard_expr
  in
  let%bind e = do_transform c.pc_rhs in
  return (c.pc_lhs, guard_opt, e)
;;
