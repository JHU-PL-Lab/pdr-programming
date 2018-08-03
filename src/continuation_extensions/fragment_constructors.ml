(**
   This module contains common operations for constructing continuation
   fragments.
*)

open Batteries;;
open Jhupllib;;

open Asttypes;;
open Parsetree;;

open Pdr_programming_utils.Variable_utils;;

open Fragment_types;;
open Transformer_monad;;

(* FIXME: aren't function parameters resolved from right to left in OCaml?
   Are we messing that up with our sequentialization here? *)
(* FIXME: right now, we're not consistently maintaining any invariants w.r.t.
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
  * The entry point of a well-formed fragment group never has an input hole.  As
    a consequence, the fragment in a pure, well-formed fragment group never has
    an input hole.
Note that ill-formed fragment groups may be intentionally constructed, i.e. to
be passed to utility routines such as [embed_nonbind].
*)

(** Some of the fragment constructors have constraints on the types of AST they
    can construct.  Pattern guards, for instance, must be pure expressions.  If
    a fragment constructor is passed an invalid expression, this exception is
    raised. *)
exception Unfragmentable_ast of string;;

(*******************************************************************************
   Stitching assertions.  Used to verify form of inputs at stitching time.
*)

exception Invalid_stitching_arguments of Fragment_uid.t * string;;

let assert_no_input_expr
    (uid : Fragment_uid.t)
    (input_expr_opt : expression option)
  : unit =
  match input_expr_opt with
  | None -> ()
  | Some _ ->
    raise @@ Invalid_stitching_arguments(
      uid, "Unexpected input expression")
;;

let assert_yes_input_expr
    (uid : Fragment_uid.t)
    (input_expr_opt : expression option)
  : expression =
  match input_expr_opt with
  | None ->
    raise @@ Invalid_stitching_arguments(uid, "Missing input expression")
  | Some e -> e
;;

let assert_evaluation_hole_function_count
    (uid : Fragment_uid.t)
    (n : int)
    (lst : (expression -> expression) list)
  : unit =
  if (List.length lst != n) then
    raise @@ Invalid_stitching_arguments(
      uid,
      Printf.sprintf "Invalid evaluation hole function count: was %d, expected %d"
        (List.length lst) n)
;;

let assert_singleton_evaluation_hole_function
    (uid : Fragment_uid.t)
    (lst : (expression -> expression) list)
  : expression -> expression =
  match lst with
  | [f] -> f
  | _ ->
    raise @@ Invalid_stitching_arguments(
      uid,
      Printf.sprintf
        "Invalid evaluation hole function count: was %d, expected 1"
        (List.length lst))
;;

let assert_extension_hole_expression_count
    (uid : Fragment_uid.t)
    (n : int)
    (lst : expression list)
  : unit =
  if (List.length lst != n) then
    raise @@ Invalid_stitching_arguments(
      uid,
      Printf.sprintf
        "Invalid extension hole expression count: was %d, expected %d"
        (List.length lst) n)
;;

let assert_singleton_extension_hole_expression
    (uid : Fragment_uid.t)
    (es : expression list)
  : expression =
  match es with
  | [e] -> e
  | _ ->
    raise @@ Invalid_stitching_arguments(
      uid,
      Printf.sprintf
        "Invalid extension hole expression count: was %d, expected 1"
        (List.length es))
;;

(*******************************************************************************
   Constructor utility functions.
*)

(** Retrieves the entry fragment from a group. *)
let get_entry_fragment (g : fragment_group) : fragment =
  Fragment_uid_map.find g.fg_entry g.fg_graph
;;

(** Determines if a fragment group is pure. *)
let is_pure (g : fragment_group) : bool =
  (* Is the entry point also the exit point? *)
  Fragment_uid_set.equal (Fragment_uid_set.singleton g.fg_entry) g.fg_exits &&
  (* Are we devoid of any extension holes? *)
  (let entry = get_entry_fragment g in
   List.is_empty entry.fragment_extension_holes
  )
;;

(** Retrieves the only fragment from a pure fragment group.  Must only be called
    on pure fragment groups. *)
let get_pure_fragment (g : fragment_group) : fragment =
  if is_pure g then
    get_entry_fragment g
  else
    raise @@ Utils.Invariant_failure
      "attempted to retrieve pure fragment from impure fragment group"
;;

(** Converts a pure fragment group into an expression.  The evaluation holes are
    transformed by identity.  Raises an exception if an impure group is
    provided. *)
let pure_fragment_group_to_expression (g : fragment_group) : expression =
  if is_pure g then
    let entry_fragment = get_entry_fragment g in
    let fns =
      List.make (List.length entry_fragment.fragment_evaluation_holes) identity
    in
    entry_fragment.fragment_code None fns []
  else
    raise @@ Utils.Invariant_failure
      "attempted to convert impure fragment group into expression"
;;

(** Determines the free variables of a fragment group. *)
let get_fragment_group_free_vars (g : fragment_group) : Var_set.t =
  g.fg_graph
  |> Fragment_uid_map.values
  |> Enum.map (fun f -> f.fragment_free_variables)
  |> Enum.fold Var_set.union Var_set.empty
;;

(** Creates a fragment from a pure expression. *)
let pure_fragment
    ?uid:(uid=None)
    (e : expression)
    (free_vars : Var_set.t)
  : fragment m =
  let%bind uid =
    match uid with
    | None -> fresh_uid ()
    | Some uid -> return uid
  in
  return
    { fragment_uid = uid;
      fragment_loc = e.pexp_loc;
      fragment_free_variables = free_vars;
      fragment_externally_bound_variables = Var_map.empty;
      fragment_input_hole = None;
      fragment_evaluation_holes =
        [ { evhd_loc = e.pexp_loc;
            evhd_target_fragment = None;
            evhd_bound_variables = Var_map.empty
          }
        ];
      fragment_extension_holes = [];
      fragment_code =
        (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
           assert_no_input_expr uid input_expr_opt;
           let f =
             assert_singleton_evaluation_hole_function uid eval_holes_fns
           in
           assert_extension_hole_expression_count uid 0 ext_holes_exprs;
           f e
        )
    }
;;

(** Creates an otherwise-pure fragment with an input hole.  The provided
    function should take an expression representing the contents to place in the
    input hole and return the expression generated by the fragment.
    Equivalently, one may think of the argument as the input hole and build the
    expression-with-a-hole accordingly. *)
let pure_fragment_with_input
    ?uid:(uid=None)
    (loc : Location.t)
    (expr_func : expression -> expression)
    (free_vars : Var_set.t)
  : fragment m =
  let%bind uid =
    match uid with
    | None -> fresh_uid ()
    | Some uid -> return uid
  in
  return
    { fragment_uid = uid;
      fragment_loc = loc;
      fragment_free_variables = free_vars;
      fragment_externally_bound_variables = Var_map.empty;
      fragment_input_hole = Some { inhd_loc = loc };
      fragment_evaluation_holes =
        [ { evhd_loc = loc;
            evhd_target_fragment = None;
            evhd_bound_variables = Var_map.empty
          }
        ];
      fragment_extension_holes = [];
      fragment_code =
        (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
           let input_expr = assert_yes_input_expr uid input_expr_opt in
           let f =
             assert_singleton_evaluation_hole_function uid eval_holes_fns
           in
           assert_extension_hole_expression_count uid 0 ext_holes_exprs;
           f (expr_func input_expr)
        )
    }
;;

(** Creates a fragment group from a pure expression. *)
let pure_singleton_fragment_group
    ?uid:(uid=None)
    (e : expression)
    (free_vars : Var_set.t)
  : fragment_group m =
  let%bind fragment = pure_fragment ~uid:uid e free_vars in
  let uid = fragment.fragment_uid in
  return
    { fg_graph = Fragment_uid_map.singleton uid fragment;
      fg_loc = e.pexp_loc;
      fg_entry = uid;
      fg_exits = Fragment_uid_set.singleton uid;
    }
;;

(** Given a fragment, transforms the expression it produces by filtering it
    through a function.  The resulting fragment is identical in every way to
    the original fragment except that its code function's output is passed
    through the provided mapping function.  This is useful for wrapping the
    output in a larger expression. *)
let fragment_code_transform
    (transform : expression -> expression)
    (fragment : fragment)
  : fragment =
  { fragment with
    fragment_code =
      (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
         let e =
           fragment.fragment_code input_expr_opt eval_holes_fns ext_holes_exprs
         in
         transform e
      )
  }
;;

(** Given a fragment with no input hole, transform the fragment's expression to
    include an input hole.  The resulting fragment is identical in every way to
    the original fragment except (1) it has an input hole and (2) the code
    function's output is passed through the provided mapping function, which has
    the ability to mention an input hole's contents.

    The provided transform function takes two arguments: the expression
    generated by the original fragment and the expression to use to fill the
    input hole (in that order).  This latter expression may be treated as the
    input hole itself, in which case the function should return the code to be
    generated by the transformed fragment.
*)
let fragment_code_transform_with_input
    (loc : Location.t)
    (transform : expression -> expression -> expression)
    (fragment : fragment)
  : fragment =
  if Option.is_some fragment.fragment_input_hole then (
    raise @@ Utils.Invariant_failure
      "fragment_code_transform_with_input provided fragment with input hole"
  );
  { fragment with
    fragment_input_hole = Some { inhd_loc = loc };
    fragment_code =
      (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
         let ie = assert_yes_input_expr fragment.fragment_uid input_expr_opt in
         let e =
           fragment.fragment_code None eval_holes_fns ext_holes_exprs
         in
         transform e ie
      )
  }
;;

(** Given a fragment, marks a set of variables as free.  Only the metadata of
    the resulting fragment is modified by this operation.  Externally bound
    variables are not affected by this function; it is possible due to shadowing
    in the original code that two different occurrences of e.g. "x" are bound by
    different fragments. *)
let fragment_metadata_free (vars : Var_set.t) (fragment : fragment) : fragment =
  { fragment with
    fragment_free_variables =
      Var_set.union fragment.fragment_free_variables vars
  }
;;

(** Given a fragment group, marks the provided set of variables as free in that
    group.  As each group represents an expression, this is as simple as marking
    each of the fragments accordingly.  Only the metadata is affected by this
    operation; no code, entry points, or exit points are modified. *)
let fragment_group_metadata_free
    (vars : Var_set.t)
    (fragment_group : fragment_group)
  : fragment_group =
  { fragment_group with
    fg_graph =
      Fragment_uid_map.map (fragment_metadata_free vars) fragment_group.fg_graph
  }
;;

(** Given a fragment, rewrites its metadata to indicate that a particular set
    of variables are bound around it.  This does not modify the code whatsoever,
    but a caller may use this routine to update the metadata of a fragment
    immediately before wrapping it within another fragment or updating its
    fragment graph to include a prior fragment which binds those variables.

    For instance, consider a well-formed fragment with UID 5 for "x + 1" that is
    free in the variable "x".  Suppose that fragment is provided to this routine
    with a mapping from "x" to type "int" with a binder UID of 4.  The returned
    value is still a fragment representing the code "x + 1", but its metadata
    show no free variables and instead ascribe the binding of "x" to an integer
    by fragment UID 4.  Afterward, the caller may independently update the graph
    in which fragment UID 5 appears to include a fragment UID 4; this latter
    fragment may represent e.g. "let x = 1 in EVAL", where EVAL is a evaluation
    hole pointing to fragment UID 5.

    This routine observes the free variable set of the provided fragment.
    Bindings which do not appear in the free variable set of the provided
    fragment are ignored.

    If the binder UID is equal to the fragment's UID, the bindings are not added
    to the externally bound set of variables.  For instance, consider the
    example above.  If, instead of adding a new fragment with UID 4 to the
    graph, we rewrite fragment UID 5 to represent "let x = 1 in x + 1", the
    variable "x" no longer needs to be satisfied by a previous fragment in
    control flow and so can be ignored by this fragment's predecessors.

    Because a fragment represents an expression containing holes, any variables
    bound by this method are added to the set of available variables at each
    of the extension and evaluation holes of the fragment (unless this binding
    is shadowed by a previous mapping already present at those holes).
*)
let fragment_metadata_bind
    (binder_uid : Fragment_uid.t)
    (bindings : core_type option Var_map.t)
    (fragment : fragment)
  : fragment =
  (* Get the applicable bindings: those which are actually free in the
     fragment. *)
  let applicable_bindings =
    bindings
    |> Var_map.filter
      (fun k _ -> Var_set.mem k fragment.fragment_free_variables)
  in
  (* Determine the updated set of free variables.  This will simply be the
     free variables which were not covered by the applicable bindings. *)
  let updated_free_variables =
    fragment.fragment_free_variables
    |> Var_set.filter (fun k -> not @@ Var_map.mem k applicable_bindings)
  in
  (* Now determine the new mapping of externally bound variables.  If the
     binder UID matches this fragment, then this map won't change: the free
     variables we just bound were bound internally.  If the binder UID doesn't
     match, we need to record it so we know where to get our data in the
     future. *)
  let updated_externally_bound_variables =
    if Fragment_uid.equal fragment.fragment_uid binder_uid then
      fragment.fragment_externally_bound_variables
    else begin
      let new_external_bindings =
        applicable_bindings
        |> Var_map.map (fun t -> (binder_uid, t))
      in
      Var_map.merge
        (fun var value1o value2o ->
           match value1o, value2o with
           | Some value1, None -> Some value1
           | None, Some value2 -> Some value2
           | None, None -> None
           | Some value1, Some value2 ->
             raise @@ Utils.Invariant_failure(
               Printf.sprintf
                 "Tried to modify binding metadata to indicate fragment %s's variable %s is bound by both fragment %s and fragment %s"
                 (Fragment_uid.show fragment.fragment_uid)
                 (Longident_value.show var)
                 (Fragment_uid.show @@ fst value1)
                 (Fragment_uid.show @@ fst value2)
             )
        )
        fragment.fragment_externally_bound_variables
        new_external_bindings
    end
  in
  (**
     The evaluation and extension holes of the fragment carry information about
     the variables which are bound at their locations.  We need to add these
     bindings to them, preferring those which are already there (as variable
     shadowing will prefer existing bindings to these new, larger-scoped
     bindings).  Note that this will include *all* variables provided by the
     call, whether they were free in this expression or not.
  *)
  let updated_evaluation_holes =
    fragment.fragment_evaluation_holes
    |> List.map
      (fun evaluation_hole ->
         { evaluation_hole with
           evhd_bound_variables =
             Var_map.union_left
               evaluation_hole.evhd_bound_variables
               bindings
         }
      )
  in
  let updated_extension_holes =
    fragment.fragment_extension_holes
    |> List.map
      (fun extension_hole ->
         { extension_hole with
           exhd_bound_variables =
             Var_map.union_left
               extension_hole.exhd_bound_variables
               bindings
         }
      )
  in
  (* That should do it.  Build and return the result. *)
  { fragment with
    fragment_free_variables = updated_free_variables;
    fragment_externally_bound_variables = updated_externally_bound_variables;
    fragment_evaluation_holes = updated_evaluation_holes;
    fragment_extension_holes = updated_extension_holes;
  }
;;

(**
   Given a fragment group, rewrites its metadata to indicate that a particular
   set of variables are bound around it.  This does not modify the graph or the
   generated code; it only updates the metadata to reflect a (presumably
   soon-to-be-enforced) future binding.  As fragment groups correspond to
   expressions containing holes, we presume the bindings provided here apply to
   the entire expression (and thus all fragments contained in this group) with
   the usual shadowing rules.  For more information on the details of this
   process, see [fragment_metadata_bind].
*)
let fragment_group_metadata_bind
    (binder_uid : Fragment_uid.t)
    (bindings : core_type option Var_map.t)
    (fragment_group : fragment_group)
  : fragment_group =
  let graph = fragment_group.fg_graph in
  let graph' =
    Fragment_uid_map.map (fragment_metadata_bind binder_uid bindings) graph
  in
  { fragment_group with
    fg_graph = graph'
  }
;;

(** Computes the union of two fragment graphs.  If the graphs have overlapping
    mappings, an exception is raised. *)
let merge_fragment_graphs
    (graph1 : fragment Fragment_uid_map.t)
    (graph2 : fragment Fragment_uid_map.t)
  : fragment Fragment_uid_map.t =
  Fragment_uid_map.merge
    (fun _ value1o value2o ->
       match value1o, value2o with
       | Some value1, None -> Some value1
       | None, Some value2 -> Some value2
       | None, None -> None
       | Some _, Some _ ->
         raise @@ Utils.Invariant_failure
           "Attempted to merge overlapping fragment graphs"
    )
    graph1 graph2
;;

(** Computes the union of two bound variable maps.  If the graphs have
    overlapping mappings, an exception is raised. *)
let merge_externally_bound_maps
    (graph1 : (Fragment_uid.t * core_type option) Var_map.t)
    (graph2 : (Fragment_uid.t * core_type option) Var_map.t)
  : (Fragment_uid.t * core_type option) Var_map.t =
  Var_map.merge
    (fun _ value1o value2o ->
       match value1o, value2o with
       | Some value1, None -> Some value1
       | None, Some value2 -> Some value2
       | None, None -> None
       | Some _, Some _ ->
         raise @@ Utils.Invariant_failure
           "Attempted to merge overlapping external binding maps"
    )
    graph1 graph2
;;

(** Replaces the entry fragment of a fragment group.  This operation removes the
    entry fragment, replacing it with the provided one, and updates the entry
    and exit points of the group accordingly.  (The exit points may be modified
    if they include the entry point which was replaced, such as in a singleton
    fragment group. *)
let replace_entry_fragment (fragment : fragment) (group : fragment_group)
  : fragment_group =
  (* Rewrite the graph to include the new fragment. *)
  let graph =
    group.fg_graph
    |> Fragment_uid_map.remove group.fg_entry
    |> Fragment_uid_map.add fragment.fragment_uid fragment
  in
  (* Rewrite any exit points which matched the old entry point.  (This is
     necessary e.g. in the casse of pure fragments. *)
  let exits =
    group.fg_exits
    |> Fragment_uid_set.map
      (fun exit_uid ->
         if exit_uid = group.fg_entry then fragment.fragment_uid else exit_uid
      )
  in
  (* If any externally-bound variables referred to the old entry point, they
     need to be adjusted to refer to the new one. *)
  let graph' =
    graph
    |> Fragment_uid_map.map
      (fun old_fragment ->
         { old_fragment with
           fragment_externally_bound_variables =
             old_fragment.fragment_externally_bound_variables
             |> Var_map.map
               (fun (binder, typ_opt) ->
                  ((if binder = group.fg_entry
                    then fragment.fragment_uid else binder),
                   typ_opt
                  )
               )
         }
      )
  in
  let result =
    { fg_graph = graph';
      fg_loc = group.fg_loc;
      fg_entry = fragment.fragment_uid;
      fg_exits = exits;
    }
  in
  result
;;

(** Rewrites all of the exit points of a given fragment group to point to a
    particular fragment.  This removes them from the list of exit points,
    yielding a group which has no exits. *)
let rewrite_exit_points_to (uid : Fragment_uid.t) (g : fragment_group) =
  let new_g =
    Fragment_uid_set.fold
      (fun exit_uid old_g ->
         let old_fragment = Fragment_uid_map.find exit_uid old_g.fg_graph in
         let new_evaluation_holes =
           old_fragment.fragment_evaluation_holes
           |> List.map
             (fun evaluation_hole ->
                { evaluation_hole
                  with evhd_target_fragment =
                         Some(Option.default uid
                                evaluation_hole.evhd_target_fragment)
                }
             )
         in
         let new_extension_holes =
           old_fragment.fragment_extension_holes
           |> List.map
             (fun extension_hole ->
                { extension_hole
                  with exhd_target_fragment =
                         Some(Option.default uid
                                extension_hole.exhd_target_fragment)
                }
             )
         in
         let new_fragment =
           { old_fragment with
             fragment_evaluation_holes = new_evaluation_holes;
             fragment_extension_holes = new_extension_holes;
           }
         in
         { old_g with
           fg_graph = Fragment_uid_map.add exit_uid new_fragment old_g.fg_graph
         }
      )
      g.fg_exits g
  in
  { new_g with
    fg_exits = Fragment_uid_set.empty
  }
;;

(* Connects dataflow between two groups.  The first group's exit points are
   attached to the entry point of the second group.  The second group's entry
   point must have an input hole into which the output of the first group can
   flow.  (Note: this means that the second group is not well-formed for
   purposes of other routines' invariants.)  If the first group is pure, then it
   will be incorporated into the entry fragment of the second group entirely.

   Consider the following pseudo-examples of fragment groups as expressions and
   the groups (as expressions) that are produced.  We use INPUT to denote the
   input hole.

      embed_nonbind "4" "Foo(INPUT)" ==> "Foo(4)"
      embed_nonbind "a==b" "if INPUT then 1 else 2" ==> "if a==b then 1 else 2"
      embed_nonbind "q" "r + INPUT" ==> "r + q"

   This function assumes that the first expression is lexically contained within
   the second expression in a position which does not bind any variables within
   either fragment group.  It then propagates free variable metadata *ONLY*; it
   does not propagate bindings from the second expression into the first.  In
   the third example above, for instance, the inputs have free variables {"q"}
   and {"r"}, respectively, and the result has free variables {"q","r"}.

   One consequence of the above is that this function is NOT suitable when the
   embedding position is one which binds variables.  For instance,

      embed_nonbind "x" "let x = 4 in INPUT"

   would not generate the correct behavior; this is not the intended purpose of
   input holes.
*)
let embed_nonbind
    (loc : Location.t) (g1 : fragment_group) (g2 : fragment_group)
  : fragment_group =
  if is_pure g1 then
    (* The first group is pure.  This means we can embed the group entirely
       within the second group. *)
    let f1 = get_pure_fragment g1 in
    let old_entry = Fragment_uid_map.find g2.fg_entry g2.fg_graph in
    if old_entry.fragment_input_hole = None then
      raise @@ Utils.Invariant_failure
        "embed_nonbind called for g2 with no input hole";
    let uid = old_entry.fragment_uid in
    let new_entry =
      { fragment_uid = uid;
        fragment_loc = loc;
        fragment_free_variables =
          Var_set.union
            f1.fragment_free_variables
            old_entry.fragment_free_variables;
        fragment_externally_bound_variables =
          (* Note: pure fragments exist in singleton graphs, so f1 can't have
             any externally bound variables. *)
          old_entry.fragment_externally_bound_variables;
        fragment_input_hole = None;
        fragment_evaluation_holes =
          (* The pure group's evaluation holes will be filled using identity
             functions so that, when it evaluates, the result will be given to
             the input hole of the second group.  So the only holes left will be
             those of the second group. *)
          old_entry.fragment_evaluation_holes;
        fragment_extension_holes =
          (* The pure group, by definition, has no extension holes. *)
          old_entry.fragment_extension_holes;
        fragment_code =
          (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
             assert_no_input_expr uid input_expr_opt;
             assert_evaluation_hole_function_count uid
               (List.length old_entry.fragment_evaluation_holes) eval_holes_fns;
             assert_extension_hole_expression_count uid
               (List.length old_entry.fragment_extension_holes) ext_holes_exprs;
             let f1_eval_holes_fns =
               List.make (List.length f1.fragment_evaluation_holes) identity
             in
             let f1_expr =
               f1.fragment_code None f1_eval_holes_fns []
             in
             old_entry.fragment_code (Some f1_expr)
               eval_holes_fns ext_holes_exprs
          )
      }
    in
    { fg_graph = Fragment_uid_map.add uid new_entry g2.fg_graph;
      fg_loc = loc;
      fg_entry = g2.fg_entry;
      fg_exits = g2.fg_exits;
    }
  else
    let g1' = rewrite_exit_points_to g2.fg_entry g1 in
    { fg_graph = merge_fragment_graphs g1'.fg_graph g2.fg_graph;
      fg_loc = loc;
      fg_entry = g1'.fg_entry;
      fg_exits = g2.fg_exits
    }
;;

(* Merges a collection of target fragment groups by collecting them under a new,
   pure expression with an input hole.  (Note: this means that the returned
   group is not well-formed for purposes of other routines' invariants.)  If all
   target groups are pure, then they will be incorporated into a singleton
   fragment group.

   The provided function should accept as its arguments an expression
   representing the content of the input hole as well as a list of expressions
   representing the code generated by the target groups; it should return the
   expression to be generated by the returned group.  This function also
   requires the provided function to generate expressions with a fixed set of
   free variables (beyond those in the target groups), which must be specified
   as an additional parameter to this function.

   This function assumes that the expressions represented by the target
   groups should be lexically contained within the expression represented by
   the returned group.  Like [embed_nonbind], the *ONLY* metadata propagated by
   this function are free variables from the target groups to the return group.
   This function does *NOT* enable the caller to externally bind free variables
   in the target expressions.  If this is necessary, the target groups should be
   preprocessed e.g. via [fragment_group_metadata_bind].

   As an example of use, consider the following pseudo-invocation, using strings
   to represent both fragments and expressions:

      embed_nonbind_pure_many
        loc
        ["4"; "5"]
        (fun input_hole [e1;e2] -> "if <HOLE> then <e1> else <e2>")
        Var_set.empty

   This invocation would return a singleton fragment group (because the target
   groups are pure) representing "if <HOLE> then 4 else 5".  As this expression
   never introduces any free variables beyond those appearing in e1 and e2, the
   free variable set is empty.
*)
let embed_nonbind_many_pure
    ?uid:(uid_opt=None)
    (loc : Location.t)
    (gs : fragment_group list)
    (wrapper : expression -> expression list -> expression)
    (free_vars : Var_set.t)
  : fragment_group m =
  let%bind entry_uid =
    match uid_opt with
    | Some uid -> return uid
    | None -> fresh_uid ()
  in
  if List.for_all is_pure gs then
    (* The target groups are pure.  This means we can embed them entirely within
       the wrapping code as a pure group. *)
    let fs = List.map get_pure_fragment gs in
    let free_vars' =
      fs
      |> List.map (fun x -> x.fragment_free_variables)
      |> Var_set.unions
      |> Var_set.union free_vars
    in
    let new_entry =
      { fragment_uid = entry_uid;
        fragment_loc = loc;
        fragment_free_variables = free_vars';
        fragment_externally_bound_variables =
          (* Pure groups never have externally bound variables (because then
             they'd have more than one fragment in them), all of these groups
             are pure, and the wrapper produces a pure expression.  So this map
             is just empty. *)
          Var_map.empty;
        fragment_input_hole = Some { inhd_loc = loc};
        fragment_evaluation_holes =
          fs
          |> List.map (fun f -> f.fragment_evaluation_holes)
          |> List.concat;
        fragment_extension_holes = [];
        fragment_code =
          (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
             let input_expr = assert_yes_input_expr entry_uid input_expr_opt in
             assert_evaluation_hole_function_count entry_uid
               (List.sum @@
                List.map
                  (fun fragment ->
                     List.length fragment.fragment_evaluation_holes)
                  fs)
               eval_holes_fns;
             List.iter
               (fun fragment ->
                  assert_extension_hole_expression_count
                    fragment.fragment_uid 0 ext_holes_exprs
               )
               fs;
             let f_exprs =
               let rec loop eval_holes_fns' fragments =
                 match fragments with
                 | [] -> []
                 | fragment::fragments' ->
                   let fragment_hole_count =
                     List.length fragment.fragment_evaluation_holes
                   in
                   let (eval_holes_fns_here, eval_holes_fns_rest) =
                     List.takedrop fragment_hole_count eval_holes_fns'
                   in
                   let expr_here =
                     fragment.fragment_code
                       None
                       eval_holes_fns_here
                       []
                   in
                   expr_here :: loop eval_holes_fns_rest fragments'
               in
               loop eval_holes_fns fs
             in
             wrapper input_expr f_exprs
          )
      }
    in
    return { fg_graph = Fragment_uid_map.singleton entry_uid new_entry;
             fg_loc = loc;
             fg_entry = entry_uid;
             fg_exits = Fragment_uid_set.singleton entry_uid;
           }
  else
    let target_entry_uids =
      gs
      |> List.enum
      |> Enum.map (fun g -> g.fg_entry)
      |> Fragment_uid_set.of_enum
    in
    let target_exit_uids =
      gs
      |> List.map (fun g -> g.fg_exits)
      |> List.fold_left Fragment_uid_set.union Fragment_uid_set.empty
    in
    let target_entry_fragments = List.map get_entry_fragment gs in
    let target_entry_eval_holes, target_entry_ext_holes =
      target_entry_fragments
      |> List.map
        (fun entry_fragment ->
           (entry_fragment.fragment_evaluation_holes,
            entry_fragment.fragment_extension_holes)
        )
      |> List.split
    in
    let new_entry_fragment =
      { fragment_uid = entry_uid;
        fragment_loc = loc;
        fragment_free_variables =
          gs
          |> List.map (fun g -> (get_entry_fragment g).fragment_free_variables)
          |> Var_set.unions
          |> Var_set.union free_vars;
        fragment_externally_bound_variables =
          gs
          |> List.map
            (fun g ->
               (get_entry_fragment g).fragment_externally_bound_variables)
          |> List.fold_left merge_externally_bound_maps Var_map.empty;
        fragment_input_hole = Some { inhd_loc = loc };
        fragment_evaluation_holes = List.concat target_entry_eval_holes;
        fragment_extension_holes = List.concat target_entry_ext_holes;
        fragment_code =
          (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
             let input_expr = assert_yes_input_expr entry_uid input_expr_opt in
             let target_entry_exprs =
               let rec loop t_frags eval_holes ext_holes eval_fns ext_exprs =
                 match t_frags, eval_holes, ext_holes with
                 | (t_frag::t_frags',
                    t_eval_holes::eval_holes',
                    t_ext_holes::ext_holes') ->
                   let t_eval_fns, eval_fns' =
                     List.takedrop (List.length t_eval_holes) eval_fns
                   in
                   let t_ext_exprs, ext_exprs' =
                     List.takedrop (List.length t_ext_holes) ext_exprs
                   in
                   let expr =
                     t_frag.fragment_code None t_eval_fns t_ext_exprs
                   in
                   expr ::
                   (loop t_frags' eval_holes' ext_holes' eval_fns' ext_exprs')
                 | ([],[],[]) ->
                   []
                 | _ ->
                   raise @@ Utils.Invariant_failure
                     "Mismatched fragment/hole counts in embed_nonbind_many_pure"
               in
               loop
                 target_entry_fragments
                 target_entry_eval_holes
                 target_entry_ext_holes
                 eval_holes_fns
                 ext_holes_exprs
             in
             wrapper input_expr target_entry_exprs
          )
      }
    in
    let new_graph =
      gs
      |> List.map (fun g -> g.fg_graph)
      |> List.fold_left merge_fragment_graphs Fragment_uid_map.empty
      |> Fragment_uid_map.filter
        (fun uid _ -> not @@ Fragment_uid_set.mem uid target_entry_uids)
      |> Fragment_uid_map.add entry_uid new_entry_fragment
    in
    return
      { fg_graph = new_graph;
        fg_loc = loc;
        fg_entry = entry_uid;
        fg_exits =
          target_exit_uids
          |> Fragment_uid_set.map
            (fun uid ->
               if Fragment_uid_set.mem uid target_entry_uids
               then entry_uid
               else uid)
      }
;;

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
      fragment_group_metadata_bind body.fg_entry bound_by_patterns body
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
    in
    let let_group = replace_entry_fragment let_entry bound_body in
    let bound_let_group =
      fragment_group_metadata_free free_in_bindings let_group
    in
    return bound_let_group
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
        fragment_group_metadata_bind body.fg_entry bound_by_pattern body
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
    |> List.map
      (fun (vars_bound_in_body,body) ->
         fragment_group_metadata_bind match_uid vars_bound_in_body body
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

and fragment_extension
    (loc : Location.t) (attributes : attributes) (ext : extension)
  : fragment_group m =
  let%bind is_continuation = is_continuation_extension ext in
  if is_continuation then
    let%bind uid = fresh_uid () in
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
    return
      { fg_graph = Fragment_uid_map.singleton uid fragment;
        fg_loc = loc;
        fg_entry = uid;
        fg_exits = Fragment_uid_set.singleton uid
      }
  else
    let e =
      { pexp_desc = Pexp_extension ext;
        pexp_loc = loc;
        pexp_attributes = attributes;
      }
    in
    pure_singleton_fragment_group e Var_set.empty

(* TODO: more constructors here *)

;;
