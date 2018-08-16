open Batteries;;
open Jhupllib;;

open Asttypes;;
open Parsetree;;

open Pdr_programming_utils.Variable_utils;;

open Fragment_types;;
open Fragment_utils;;
open Transformer_monad;;

type extension_handler =
  Location.t -> attributes -> extension -> fragment_group m
;;

exception Transformation_failure of string loc;;

(* FIXME: aren't function parameters resolved from right to left in OCaml?
   Are we messing that up with our sequentialization here? *)
(* FIXME: right now, we're not consistently maintaining many invariants w.r.t.
   uniqueness of UIDs.  Here's a good policy given the performance and
   logistical constraints:
     * Smart constructors are guaranteed to produce expressions with internally
       distinct UIDs.
     * Smart constructors can handle arguments with overlapping UIDs.
     * Smart constructors do NOT guarantee any uniqueness relationship between
       their arguments and their return values.
   Right now, the second point above is not handled in some cases.
*)

(* #############################################################################
   TODO:
   We need to adjust how variable bindings are handled.  Presently, we're
   tracking sets of variables which are free as well as dictionaries of bound
   variables.  Putting these back together after fragment group construction is
   quite difficult as we don't have information about the *circumstances* under
   which those variables were bound.  Instead, consider the following:
   * Each fragment maintains a set of free variables (like it does now).
   * Each fragment also maintains a set of variables bound in them by other
     fragments.  For instance, if Fragment 1 has x free and Fragment 2 is later
     constructed around Fragment 1, then Fragment 1 is adjusted to remove x from
     the free set but to add a mapping indicating that x was bound by Fragment 2
     (storing type information if it is available).
   This strategy should make it possible to do what we need to do: understand
   what information needs to be transmitted by the generated continuations
   between each fragment.  Note that it is possible for the same variable name
   to appear twice in a single closure (due to how control flow is linearized
   and scope is no longer preserved), so fresh names may need to be generated to
   represent these values.
   ########################################################################## *)

(*
The fragment group construction process maintains the following definitions and
invariants:
  * A fragment group constructed from expressions containing no continuation
    extensions is "pure".  Other fragment groups are "impure".
  * Pure fragment groups always contain exactly one fragment.  This fragment is
    the entry point and sole exit point.
  * The fragment in a pure fragment group contains no extension holes.
  * The entry point of a well-formed fragment group never has an input hole.
    Note that well-formedness is an orthogonal property to purity: a fragment
    may be pure and ill-formed while another fragment may be impure and
    well-formed.
Ill-formed fragment groups may be intentionally constructed, i.e. to be passed
to utility routines such as [embed_nonbind].

Construction of fragments proceeds bottom-up.  At each step, the resulting
fragment group has a set of invariant properties:
  * Each fragment maintains a set of variables which are free in its own code.
    Fragments do *not* track free variables in the code of other fragments
    (whether lexically contained or following in control flow).  Ensuring that
    continuations carry the necessary data is managed by control flow analysis
    after a full fragment group is constructed.
  * Fragments *do* keep track of how their free variables are bound.  If a
    fragment's free variable is bound by another fragment, this is recorded as
    an *externally bound* variable.
  * A fragment group always represents a single expression.  Constructors always
    enclose the expression represented by a fragment group.  As a result, the
    only fragment of a fragment group whose code is modified is the entry
    fragment.  Metadata, on the other hand, may change for any fragment in a
    group.
  * Because fragment groups are always enclosed by constructors, any variable
    binding to the group applies to every fragment uniformally: if the variable
    is free in that fragment, it is bound.  As a consequence of this uniformity,
    a given variable may only be externally bound once.  (The same variable may
    be shadowed within the fragment's code, but that does not affect external
    binding.)
  * All non-entry fragments in a group have input holes.
*)

(*******************************************************************************
   Constructor-aware utility functions.
*)

(* Sequentializes the execution of multiple groups.  If all groups are pure,
   this is as simple as generating expressions for each group and passing them
   to a final creation routine.  Impure groups are addressed by let-binding the
   results of execution to variables and creating a chain of fragments which
   pass along the results; the final fragment in the chain is constructed by
   passing variable expressions representing the results of the fragments into
   the final creation routine.  The resulting fragment group will evaluate each
   of the input groups in the same order that they are provided in the input
   list.  None of the input groups are permitted to have an input hole.
*)
let rec sequentialize_fragment_groups
    (loc : Location.t)
    (gs : fragment_group list)
    (create : expression list -> expression)
  : fragment_group m =
  (* We want to fold over the expressions, building up both the fragment group
     that evaluates gs as well as the expression that produces the tuple.
     Sadly, we can't do this as it means we wouldn't create the base case (the
     target expression) until after we fold.  So we'll have to do this in a few
     steps:
      1. Loop over the gs to find the last impure one.  All of the expressions
         after that can be given to the tuple verbatim.
      2. Pick fresh variable names for the let bindings we will build for all of
         the other expressions.
      3. Build the tuple using the fresh variables and pure expressions.  Use it
         to construct a pure exit fragment to use as the base case.
      4. Finally, loop over the other groups and build up the necessary
         let-bindings.
  *)
  (* Separate the suffix of gs which is pure into its own list. *)
  let pure_gs, other_gs = List.span is_pure @@ List.rev gs in
  (* Get the pure expressions from that suffix; put them in correct order. *)
  let pure_exprs =
    List.rev @@ List.map pure_fragment_group_to_expression pure_gs
  in
  (* Pick variable names for the other gs. *)
  let%bind other_varnames_enum =
    other_gs
    |> List.enum
    |> mapM (fun _ -> fresh_var ())
  in
  let other_varnames = List.of_enum other_varnames_enum in
  (* Build up appropriate expressions for the creator function. *)
  let exprs =
    other_varnames
    |> List.combine other_gs
    |> List.fold_left
      (fun lst (g,other_varname) ->
         let expr =
           { pexp_desc =
               Pexp_ident(
                 { txt = Longident.Lident other_varname;
                   loc = g.fg_loc
                 });
             pexp_loc = g.fg_loc;
             pexp_attributes = [];
           }
         in
         expr::lst
      ) pure_exprs
  in
  (* Create the base fragment group. *)
  let base_expr = create exprs in
  let%bind base_group =
    pure_singleton_fragment_group
      base_expr (free_expr_vars base_expr)
  in
  (* Now loop over the remaining groups, creating let bindings for each one so
     as to close the fragment we just created. *)
  let%bind result_group =
    other_gs
    |> List.combine other_varnames
    |> List.fold_left
      (fun groupM (other_varname, other_g) ->
         let%bind group = groupM in
         let other_loc = other_g.fg_loc in
         let varp = { ppat_desc = Ppat_var
                          { txt = other_varname;
                            loc = other_loc
                          };
                      ppat_loc = other_loc;
                      ppat_attributes = []
                    }
         in
         fragment_let
           other_g.fg_loc [] Nonrecursive [(varp, other_g, [], loc)] group
      )
      (return base_group)
  in
  return result_group

(*******************************************************************************
   Constructors.
*)

and fragment_ident
    (loc : Location.t) (attributes : attributes)
    (x : Longident.t Asttypes.loc)
  : fragment_group m =
  let e =
    { pexp_desc = Pexp_ident x;
      pexp_attributes = attributes;
      pexp_loc = loc
    }
  in
  pure_singleton_fragment_group e @@ Var_set.singleton x.txt

and fragment_constant
    (loc : Location.t) (attributes : attributes)
    (c : constant)
  : fragment_group m =
  let e =
    { pexp_desc = Pexp_constant c;
      pexp_attributes = attributes;
      pexp_loc = loc
    }
  in
  pure_singleton_fragment_group e Var_set.empty

(* TODO: more constructors here *)

and fragment_let
    (loc : Location.t) (attributes : attributes)
    (rec_flag : rec_flag)
    (bindings : (pattern * fragment_group * attributes * Location.t) list)
    (body : fragment_group)
  : fragment_group m =
  let binding_fragment_groups = List.map (fun (_,g,_,_) -> g) bindings in
  if List.for_all is_pure binding_fragment_groups then
    (* All of the bindings are pure.  This means we can just reconstruct it as
       a basic let binding without worrying about control flow.  The body may
       not be pure, so we'll merge all of this let-binding stuff with the entry
       fragment of the body group.  The evaluation and extension holes will
       come from that entry fragment, but are modified by the patterns in the
       variable bindings. *)
    let bound_by_patterns : core_type option Var_map.t =
      bindings
      |> List.map (fun (pattern,_,_,_) -> bound_pattern_vars_with_type pattern)
      |> List.rev
      |> List.fold_left Var_map.union_left Var_map.empty
    in
    (* FIXME: the below does not address free variables in pattern guards *)
    let free_in_bindings : Var_set.t =
      bindings
      |> List.map (fun (_,g,_,_) -> get_fragment_group_free_vars g)
      |> Var_set.unions
    in
    (* We're going to be modifying the entry point of the group in order to do
       the binding, so credit it for doing the binding work. *)
    let bound_body =
      fragment_group_metadata_bind loc body.fg_entry bound_by_patterns body
    in
    let bound_body_entry = get_entry_fragment bound_body in
    let let_entry =
      fragment_code_transform
        (fun e ->
           let pure_bindings =
             List.map
               (fun (bpat,bgrp,battr,bloc) ->
                  let e' = pure_fragment_group_to_expression bgrp in
                  { pvb_pat = bpat;
                    pvb_expr = e';
                    pvb_attributes = battr;
                    pvb_loc = bloc
                  }
               ) bindings
           in
           { pexp_desc = Pexp_let(rec_flag, pure_bindings, e);
             pexp_loc = loc;
             pexp_attributes = attributes
           }
        )
        bound_body_entry
      |> fragment_metadata_free free_in_bindings
    in
    let let_group = replace_entry_fragment let_entry bound_body in
    return let_group
  else
    begin
      (* At least one of the bindings isn't pure.  Since a single let binding is
         processed as a single block and we need to manipulate control flow here,
         we only admit the case of a single, non-recursive impure let binding.
         While it might be possible to admit other cases in the future, their
         meanings are not immediately clear. *)
      if rec_flag = Recursive then
        raise @@ Unfragmentable_ast
          "recursive let binding with impure binding expression";
      if List.length bindings != 1 then
        raise @@ Unfragmentable_ast
          "let-and binding with impure binding expression";
      let (binding_pattern,
           binding_fragment_group,
           binding_attributes,
           binding_location
          ) =
        List.first bindings
      in
      (* Since we only have one binding to worry about, this case is pretty
         similar to other wrapper cases (e.g. fragment_constructor).  We have
         an inner expression -- the binding fragment group -- which we want to
         run first and then pass to the outer expression: the body fragment
         group.  The only difference is that we also want to modify the exit
         points of the body to ensure that they know about the new variables
         bound by the pattern.  So we'll...
          1. Modify the entry fragment of the body group to include an input
             hole, the let binding expression, and exit points with the
             appropriate variables bound, and
          2. Use the binding fragment group to supply this modified body group
             with a value for its input hole.
      *)
      let bound_by_pattern = bound_pattern_vars_with_type binding_pattern in
      (* We're going to be modifying the entry point of the group in order to do
         the binding, so credit it for doing the binding work. *)
      let bound_body =
        fragment_group_metadata_bind loc body.fg_entry bound_by_pattern body
      in
      let bound_body_entry = get_entry_fragment bound_body in
      let bound_let_entry =
        bound_body_entry
        |> fragment_code_transform_with_input loc
          (fun expr input_hole ->
             let binding =
               { pvb_pat = binding_pattern;
                 pvb_expr = input_hole;
                 pvb_attributes = binding_attributes;
                 pvb_loc = binding_location;
               }
             in
             { pexp_desc = Pexp_let(rec_flag, [binding], expr);
               pexp_loc = loc;
               pexp_attributes = attributes
             }
          )
      in
      (* Note: we're intentionally leaving the free variables in the binding
         expression out of the bound_let here.  This is because the act of
         connecting the two fragments will transfer free variables
         appropriately. *)
      let bound_let = replace_entry_fragment bound_let_entry bound_body in
      (* At this point, all of the metadata regarding bindings has been
         updated appropriately.  As a result, inserting the binding expression
         into the let expression doesn't introduce any new binding information
         and we can use a simple control flow connection routine to embed one
         within the other. *)
      let result = embed_nonbind loc binding_fragment_group bound_let in
      return result
    end

(* TODO: more constructors here *)

and fragment_apply
    (loc : Location.t) (attributes : attributes)
    (g_fn : fragment_group) (args : (Asttypes.arg_label * fragment_group) list)
  : fragment_group m =
  let labels,g_args = List.split args in
  sequentialize_fragment_groups loc (g_fn::g_args)
    (fun es ->
       let e_fn = List.hd es in
       let e_args = List.tl es in
       let args = List.combine labels e_args in
       { pexp_desc = Pexp_apply(e_fn,args);
         pexp_loc = loc;
         pexp_attributes = attributes;
       }
    )

(* TODO: more constructors here *)

and fragment_match
    (loc : Location.t) (attributes : attributes)
    (g : fragment_group)
    (cs : (pattern * fragment_group option * fragment_group) list)
  : fragment_group m =
  (* This is really just a generalization of the control flow technique used in
     the fragment_ifthenelse function.  It's combined with the binding of
     variables from patterns, but that's largely orthogonal. *)
  let%bind match_uid = fresh_uid () in
  (* Extract the pieces of each case *)
  let patterns = cs |> List.map (fun (p,_,_) -> p) in
  let guards =
    cs
    |> List.map (fun (_,guard,_) -> guard)
    |> List.map
      (Option.map @@
       fun guard_fg ->
       if is_pure guard_fg then
         pure_fragment_group_to_expression guard_fg
       else
         raise @@ Unfragmentable_ast
           "fragment_match: pattern guards must not contain continuation extensions"
      )
  in
  let bodies = cs |> List.map (fun (_,_,match_body) -> match_body) in
  let locs = cs |> List.map (fun (p,_,_) -> p.ppat_loc) in
  (* Determine variable bindings so we can adjust the holes in the cases
     based on which variables their patterns bind. *)
  let vars_bound_in_bodies =
    patterns
    |> List.map bound_pattern_vars_with_type
  in
  (* FIXME: we do not address free variables in pattern guards *)
  let bound_bodies =
    bodies
    |> List.combine vars_bound_in_bodies
    |> List.combine locs
    |> List.map
      (fun (loc,(vars_bound_in_body,body)) ->
         fragment_group_metadata_bind loc match_uid vars_bound_in_body body
      )
  in
  let%bind match_with_input_hole =
    embed_nonbind_many_pure
      ~uid:(Some match_uid)
      loc
      bound_bodies
      (fun input_hole body_exprs ->
         let cases =
           patterns
           |> List.combine guards
           |> List.combine body_exprs
           |> List.map
             (fun (case_expr, (guard, pattern)) ->
                { pc_lhs = pattern;
                  pc_guard = guard;
                  pc_rhs = case_expr
                }
             )
         in
         { pexp_desc = Pexp_match(input_hole, cases);
           pexp_loc = loc;
           pexp_attributes = attributes
         }
      )
      Var_set.empty
  in
  return @@ embed_nonbind loc g match_with_input_hole

(* TODO: more constructors here *)

and fragment_tuple
    (loc : Location.t) (attributes : attributes)
    (gs : fragment_group list)
  : fragment_group m =
  sequentialize_fragment_groups loc gs
    (fun es ->
       { pexp_desc = Pexp_tuple es;
         pexp_loc = loc;
         pexp_attributes = attributes;
       }
    )

(* TODO: more constructors here *)

and fragment_construct
    (loc : Location.t) (attributes : attributes)
    (name : Longident.t Asttypes.loc) (go : fragment_group option)
  : fragment_group m =
  match go with
  | None ->
    let e =
      { pexp_desc = Pexp_construct(name, None);
        pexp_attributes = attributes;
        pexp_loc = loc;
      }
    in
    pure_singleton_fragment_group e Var_set.empty
  | Some g ->
    let%bind constructor_fragment =
      pure_fragment_with_input loc
        (fun input_hole ->
           { pexp_desc = Pexp_construct(name, Some input_hole);
             pexp_loc = loc;
             pexp_attributes = attributes
           }
        )
        Var_set.empty
    in
    let uid = constructor_fragment.fragment_uid in
    let constructor_group =
      { fg_graph = Fragment_uid_map.singleton uid constructor_fragment;
        fg_loc = loc;
        fg_entry = uid;
        fg_exits = Fragment_uid_set.singleton uid;
      }
    in
    return @@ embed_nonbind loc g constructor_group

(* TODO: more constructors here *)

and fragment_ifthenelse
    (loc : Location.t) (attributes : attributes)
    (g1 : fragment_group) (g2 : fragment_group) (g3 : fragment_group)
  : fragment_group m =
  let%bind ifthenelse_hole_group =
    embed_nonbind_many_pure
      loc
      [g2;g3]
      (fun input_hole embed_exprs ->
         match embed_exprs with
         | [then_expr;else_expr] ->
           { pexp_desc = Pexp_ifthenelse(input_hole, then_expr, Some else_expr);
             pexp_loc = loc;
             pexp_attributes = attributes
           }
         | _ ->
           raise @@ Utils.Invariant_failure(
             Printf.sprintf
               "In fragment_ifthenelse, embed_nonbind_many_pure returned %d embed_exprs when two groups were provided."
               (List.length embed_exprs))
      )
      Var_set.empty
  in
  return @@ embed_nonbind loc g1 ifthenelse_hole_group

(* TODO: more constructors here *)

and fragment_constraint
    (loc : Location.t) (attributes : attributes)
    (g : fragment_group) (t : core_type)
  : fragment_group m =
  return (
    g
    |> fragment_group_code_transform
      (fun e ->
         { pexp_desc = Pexp_constraint(e, t);
           pexp_loc = loc;
           pexp_attributes = attributes
         }
      )
  )

(* TODO: more constructors here *)

and fragment_extension
    (loc : Location.t)
    (attributes : attributes)
    (name : string loc)
    (body_opt : fragment_group option)
  : fragment_group m =
  match body_opt with
  | None ->
    pure_singleton_fragment_group
      { pexp_desc = Pexp_extension(name, PStr([]));
        pexp_loc = loc;
        pexp_attributes = attributes;
      }
      Var_set.empty
  | Some body ->
    return @@
    fragment_group_code_transform
      (fun e ->
         let str = [ { pstr_desc = Pstr_eval(e, []);
                       pstr_loc = loc;
                     }
                   ]
         in
         { pexp_desc = Pexp_extension(name, PStr(str));
           pexp_loc = loc;
           pexp_attributes = attributes
         }
      )
      body

(* TODO: more constructors here *)

and fragment_continuation
    (extension_handler : extension_handler)
    (loc : Location.t)
    (attributes : attributes)
    (extension : extension)
  : fragment_group m =
  Pervasives.ignore attributes;
  let%bind uid = fresh_uid () in
  let make_extension_group ext =
    let fragment =
      { fragment_uid = uid;
        fragment_loc = loc;
        fragment_free_variables = Var_set.empty;
        fragment_externally_bound_variables = Var_map.empty;
        fragment_input_hole = None;
        fragment_evaluation_holes = [];
        fragment_extension_holes =
          [ { exhd_loc = loc;
              exhd_extension = ext;
              exhd_bound_variables = Var_map.empty;
              exhd_target_fragment = None;
            }
          ];
        fragment_code =
          (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
             assert_no_input_expr uid input_expr_opt;
             assert_evaluation_hole_function_count uid 0 eval_holes_fns;
             let e =
               assert_singleton_extension_hole_expression uid ext_holes_exprs
             in
             e
          )
      }
    in
      { fg_graph = Fragment_uid_map.singleton uid fragment;
        fg_loc = loc;
        fg_entry = uid;
        fg_exits = Fragment_uid_set.singleton uid
      }
  in
  (* If the extension has an expression payload, then we should give it a fresh
     variable name.  This way, the payload is exposed to the outside world and
     is visible as a free variable. *)
  match snd extension with
  | PStr([]) ->
    (* This extension has no payload.  Leave it alone. *)
    return @@ make_extension_group extension
  | PStr([{ pstr_desc = Pstr_eval(e,attrs); pstr_loc = str_loc}]) ->
    (* This extension has a payload.  Create a fresh variable, use that as the
       payload, and then let-bind the result so that the variables in the
       payload are bound properly.
    *)
    let%bind x = fresh_var () in
    let extension' =
      (fst extension,
       PStr([
           { pstr_desc =
               Pstr_eval(
                 { pexp_desc =
                     Pexp_ident(Location.mkloc (Longident.Lident x) loc);
                   pexp_loc = loc;
                   pexp_attributes = [];
                 },
                 []);
             pstr_loc = str_loc;
           }
         ])
      )
    in
    let base_group = make_extension_group extension' in
    let%bind payload_group = do_transform extension_handler e in
    base_group
    |> fragment_let loc attrs Nonrecursive
      [({ ppat_desc = Ppat_var(Location.mkloc x loc);
          ppat_loc = loc;
          ppat_attributes = [];
        },
        payload_group,
        [],
        loc
       )
      ]
    | _ ->
      raise @@ Utils.Not_yet_implemented(
        Printf.sprintf
          "continuation extension with multiple payloads at %s"
          (Pp_utils.pp_to_string Location.print loc)
      )

and fragment_nondeterminism
    (loc : Location.t)
    (attributes : attributes)
    (groups : fragment_group list)
  : fragment_group m =
  Pervasives.ignore attributes;
  nondeterministic_fragment_group loc groups

and do_transform
    (extension_handler : extension_handler)
    (e : expression)
  : fragment_group m =
  let recurse = do_transform extension_handler in
  let loc = e.pexp_loc in
  let attrs = e.pexp_attributes in
  try
    begin
      match e.pexp_desc with
      | Parsetree.Pexp_ident x ->
        fragment_ident loc attrs x
      | Parsetree.Pexp_constant c ->
        fragment_constant loc attrs c
      | Parsetree.Pexp_let(rec_flag,bindings,body) ->
        let%bind bindings' = do_transform_bindings extension_handler bindings in
        let%bind body' = recurse body in
        fragment_let loc attrs rec_flag bindings' body'
      | Parsetree.Pexp_function _ ->
        raise @@ Utils.Not_yet_implemented("transform: Pexp_function")
      | Parsetree.Pexp_fun(_,_,_,_) ->
        raise @@ Utils.Not_yet_implemented("transform: Pexp_fun")
      | Parsetree.Pexp_apply(fn,args) ->
        let%bind g_fn = recurse fn in
        let labels,e_args = List.split args in
        let%bind g_args = mapM recurse @@ List.enum e_args in
        let args' = List.combine labels @@ List.of_enum g_args in
        fragment_apply loc attrs g_fn args'
      | Parsetree.Pexp_match(e,cases) ->
        let%bind g = recurse e in
        let%bind fcases =
          lift1 List.of_enum @@
          mapM (do_transform_case extension_handler) @@ List.enum cases
        in
        fragment_match loc attrs g fcases
      | Parsetree.Pexp_try(_,_) ->
        raise @@ Utils.Not_yet_implemented("transform: Pexp_try")
      | Parsetree.Pexp_tuple(es) ->
        let%bind gs = mapM recurse @@ List.enum es in
        fragment_tuple loc attrs @@ List.of_enum gs
      | Parsetree.Pexp_construct(name,eo) ->
        let%bind go =
          match eo with
          | Some e -> lift1 Option.some @@ recurse e
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
        let%bind g1 = recurse e1 in
        let%bind g2 = recurse e2 in
        let%bind g3 = recurse e3 in
        fragment_ifthenelse loc attrs g1 g2 g3
      | Parsetree.Pexp_sequence(_,_) ->
        raise @@ Utils.Not_yet_implemented("transform: Pexp_sequence")
      | Parsetree.Pexp_while(_,_) ->
        raise @@ Utils.Not_yet_implemented("transform: Pexp_while")
      | Parsetree.Pexp_for(_,_,_,_,_) ->
        raise @@ Utils.Not_yet_implemented("transform: Pexp_for")
      | Parsetree.Pexp_constraint(e,t) ->
        let%bind g = recurse e in
        fragment_constraint loc attrs g t
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
        extension_handler loc attrs ext
      | Parsetree.Pexp_unreachable  ->
        raise @@ Utils.Not_yet_implemented("transform: Pexp_unreachable")
    end
  with
  | Transformation_failure(locmsg) ->
    let errloc = locmsg.loc in
    let errmsg = locmsg.txt in
    let%bind msg_group =
      fragment_constant errloc [] @@ Pconst_string(errmsg,None)
    in
    fragment_extension errloc [] (Location.mkloc "ocaml.error" errloc)
      (Some msg_group)

and do_transform_case
    (extension_handler : extension_handler)
    (c : case)
  : (pattern * fragment_group option * fragment_group) m =
  let%bind guard_opt =
    match c.pc_guard with
    | None -> return None
    | Some guard_expr ->
      Option.some <$> do_transform extension_handler guard_expr
  in
  let%bind e = do_transform extension_handler c.pc_rhs in
  return (c.pc_lhs, guard_opt, e)

and do_transform_bindings
    (extension_handler : extension_handler)
    (bindings : value_binding list)
  : (pattern * fragment_group * attributes * Warnings.loc) list m =
  bindings
  |> List.enum
  |> mapM
    (fun binding ->
       let%bind bind_expr =
         do_transform extension_handler binding.pvb_expr
       in
       return
         (binding.pvb_pat,
          bind_expr,
          binding.pvb_attributes,
          binding.pvb_loc)
    )
  |> lift1 List.of_enum
;;
