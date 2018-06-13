(**
   This module contains common operations for constructing continuation
   fragments.
*)

open Batteries;;
open Jhupllib;;

open A_normalizer;;
open Asttypes;;
open Continuation_fragment_types;;
open Continuation_transformer_monad;;
open Parsetree;;
open Variable_utils;;

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

(** Computes the union of two fragment graphs.  If the graphs have overlapping
    mappings, an exception is raised. *)
let merge_fragment_graphs
    (graph1 : fragment Fragment_uid_map.t)
    (graph2 : fragment Fragment_uid_map.t)
  : fragment Fragment_uid_map.t =
  Fragment_uid_map.merge
    (fun uid value1o value2o ->
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

(** Replaces the entry fragment of a fragment group.  This operation removes the
    entry fragment, replacing it with the provided one, and updates the entry
    and exit points of the group accordingly.  (The exit points may be modified
    if they include the entry point which was replaced, such as in a singleton
    fragment group. *)
let replace_entry_fragment (fragment : fragment) (group : fragment_group)
  : fragment_group =
  let graph =
    group.fg_graph
    |> Fragment_uid_map.remove group.fg_entry
    |> Fragment_uid_map.add fragment.fragment_uid fragment
  in
  let exits =
    group.fg_exits
    |> Fragment_uid_set.map
      (fun exit_uid ->
         if exit_uid = group.fg_entry then fragment.fragment_uid else exit_uid
      )
  in
  { fg_graph = graph;
    fg_loc = group.fg_loc;
    fg_entry = fragment.fragment_uid;
    fg_exits = exits;
  }
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
   flow.  If the first group is pure, then it will be incorporated into the
   entry fragment of the second group entirely.
*)
let connect_dataflow
    (loc : Location.t) (g1 : fragment_group) (g2 : fragment_group)
  : fragment_group =
  if is_pure g1 then
    let f1 = get_pure_fragment g1 in
    let old_entry = Fragment_uid_map.find g2.fg_entry g2.fg_graph in
    if old_entry.fragment_input_hole = None then
      raise @@ Utils.Invariant_failure
        "connect_dataflow called for g2 with no input hole";
    let uid = old_entry.fragment_uid in
    let new_entry =
      { fragment_uid = uid;
        fragment_loc = loc;
        fragment_free_variables =
          Var_set.union
            f1.fragment_free_variables old_entry.fragment_free_variables;
        fragment_input_hole = None;
        fragment_evaluation_holes = old_entry.fragment_evaluation_holes;
        fragment_extension_holes = old_entry.fragment_extension_holes;
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
      base_expr (Variable_utils.free_expr_vars base_expr)
  in
  (* Now loop over the remaining groups, creating let bindings for each one so
     as to close the fragment we just created. *)
  let%bind result_group =
    other_gs
    |> List.combine other_varnames
    |> List.fold_left
      (fun groupM (other_varname, other_g) ->
         let%bind group = groupM in
         let loc = other_g.fg_loc in
         let varp = { ppat_desc = Ppat_var { txt = other_varname; loc = loc };
                      ppat_loc = loc;
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
    let%bind uid = fresh_uid () in
    let binding_fragments =
      List.map get_pure_fragment binding_fragment_groups
    in
    let body_entry = get_entry_fragment body in
    let bound_in_body =
      List.map (fun (p,_,_,_) -> p) bindings
      |> List.map bound_pattern_vars_with_type
      |> Var_map.disjoint_unions
    in
    let bound_in_bindings =
      if rec_flag = Recursive then bound_in_body else Var_map.empty
    in
    let fragment =
      { fragment_uid = uid;
        fragment_loc = loc;
        fragment_free_variables =
          Var_set.union body_entry.fragment_free_variables @@
          Var_set.diff
            (Var_set.unions @@
             List.map (fun f -> f.fragment_free_variables) binding_fragments) @@
          Var_set.of_enum @@ Var_map.keys bound_in_bindings;
        fragment_input_hole = None;
        fragment_evaluation_holes =
          body_entry.fragment_evaluation_holes
          |> List.map
            (fun eval_hole ->
               { eval_hole with
                 evhd_bound_variables =
                   Var_map.union_left
                     eval_hole.evhd_bound_variables bound_in_body
               }
            );
        fragment_extension_holes =
          body_entry.fragment_extension_holes
          |> List.map
            (fun ext_hole ->
               { ext_hole with
                 exhd_bound_variables =
                   Var_map.union_left
                     ext_hole.exhd_bound_variables bound_in_body
               }
            );
        fragment_code =
          (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
             assert_no_input_expr uid input_expr_opt;
             let binding_exprs =
               binding_fragment_groups
               |> List.map pure_fragment_group_to_expression
             in
             let bindings =
               List.map2
                 (fun e (p,_,a,l) ->
                    { pvb_pat = p;
                      pvb_expr = e;
                      pvb_attributes = a;
                      pvb_loc = l;
                    }
                 ) binding_exprs bindings
             in
             let body =
               body_entry.fragment_code None eval_holes_fns ext_holes_exprs
             in
             { pexp_desc = Pexp_let(rec_flag, bindings, body);
               pexp_loc = loc;
               pexp_attributes = attributes;
             }
          )
      }
    in
    return @@ replace_entry_fragment fragment body
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
         bound by the pattern.  So we'll
          1. Modify the entry fragment of the body group to include an input
             hole, the let binding expression, and exit points with the
             appropriate variables bound, and
          2. Use the binding fragment group to supply this modified body group
             with a value for its input hole.
      *)
      let%bind let_uid = fresh_uid () in
      let body_entry = get_entry_fragment body in
      let bound_by_pattern = bound_pattern_vars_with_type binding_pattern in
      let let_fragment =
        { fragment_uid = let_uid;
          fragment_loc = loc;
          fragment_free_variables =
            Var_set.diff body_entry.fragment_free_variables @@
            Var_set.of_enum @@ Var_map.keys bound_by_pattern;
          fragment_input_hole = Some { inhd_loc = loc };
          fragment_evaluation_holes =
            body_entry.fragment_evaluation_holes
            |> List.map
              (fun eval_hole ->
                 { eval_hole with
                   evhd_bound_variables =
                     Var_map.union_left
                       eval_hole.evhd_bound_variables bound_by_pattern
                 }
              );
          fragment_extension_holes =
            body_entry.fragment_extension_holes
            |> List.map
              (fun ext_hole ->
                 { ext_hole with
                   exhd_bound_variables =
                     Var_map.union_left
                       ext_hole.exhd_bound_variables bound_by_pattern
                 }
              );
          fragment_code =
            (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
               let input_expr = assert_yes_input_expr let_uid input_expr_opt in
               let body_expr =
                 body_entry.fragment_code None eval_holes_fns ext_holes_exprs
               in
               { pexp_desc =
                   Pexp_let(
                     rec_flag,
                     [ { pvb_pat = binding_pattern;
                         pvb_expr = input_expr;
                         pvb_attributes = binding_attributes;
                         pvb_loc = binding_location;
                       }
                     ],
                     body_expr);
                 pexp_loc = loc;
                 pexp_attributes = attributes
               }
            )
        }
      in
      let let_fragment_group = replace_entry_fragment let_fragment body in
      return @@ connect_dataflow loc binding_fragment_group let_fragment_group
    end



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
  let body_entry_points = bodies |> List.map get_entry_fragment in
  let match_eval_holes =
    body_entry_points
    |> List.map (fun fragment -> fragment.fragment_evaluation_holes)
    |> List.concat
  in
  let match_ext_holes =
    body_entry_points
    |> List.map (fun fragment -> fragment.fragment_extension_holes)
    |> List.concat
  in
  (* We'll now create a fragment representing the match itself.  We'll leave the
     match subject open -- the fragment will have an input hole there -- so we
     can merge it with the actual subject fragment later.  This match fragment
     will carry the patterns and entry fragments of each case. *)
  let match_fragment =
    { fragment_uid = match_uid;
      fragment_loc = loc;
      fragment_free_variables =
        Var_set.unions @@
        List.map2
          (fun body bound_vars ->
             Var_set.diff body.fragment_free_variables @@
             Var_set.of_enum @@ Var_map.keys bound_vars
          )
          body_entry_points vars_bound_in_bodies;
      fragment_input_hole = Some { inhd_loc = loc };
      fragment_evaluation_holes =
        List.map2
          (fun body bound_vars ->
             body.fragment_evaluation_holes
             |> List.map
               (fun eval_hole ->
                  { eval_hole with
                    evhd_bound_variables =
                      Var_map.union_left
                        eval_hole.evhd_bound_variables bound_vars
                  }
               )
          ) body_entry_points vars_bound_in_bodies
        |> List.concat;
      fragment_extension_holes =
        List.map2
          (fun body bound_vars ->
             body.fragment_extension_holes
             |> List.map
               (fun ext_hole ->
                  { ext_hole with
                    exhd_bound_variables =
                      Var_map.union_left
                        ext_hole.exhd_bound_variables bound_vars
                  }
               )
          ) body_entry_points vars_bound_in_bodies
        |> List.concat;
      fragment_code =
        (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
           let input_expr = assert_yes_input_expr match_uid input_expr_opt in
           (* We've been provided a bunch of values to fill the holes.  Above,
              the holes for the match are described as a concatenation of the
              holes for each case in order.  The caller will have provided fill
              values in a list to match that list of holes.  Here, we'll split
              the values list into a series of lists which correspond to the
              holes for each case. *)
           assert_evaluation_hole_function_count match_uid
             (List.length match_eval_holes) eval_holes_fns;
           assert_extension_hole_expression_count match_uid
             (List.length match_ext_holes) ext_holes_exprs;
           let carve_up
               (type a) (type b) (in_list : a list) (template : b list list)
             : a list list =
             let rec loop in_list' template' =
               match template' with
               | [] -> []
               | h::t ->
                 let hl,tl = List.takedrop (List.length h) in_list' in
                 hl::loop tl t
             in
             loop in_list template
           in
           let eval_holes_fns_per_case =
             carve_up eval_holes_fns @@
             (List.map (fun fragment -> fragment.fragment_evaluation_holes)
                body_entry_points)
           in
           let ext_holes_exprs_per_case =
             carve_up ext_holes_exprs @@
             (List.map (fun fragment -> fragment.fragment_extension_holes)
                body_entry_points)
           in
           (* Having separated the holes on a per-case basis, we can now
              construct expressions for each case by providing the appropriate
              fill values. *)
           let case_exprs =
             ext_holes_exprs_per_case
             |> List.combine eval_holes_fns_per_case
             |> List.combine body_entry_points
             |> List.map
               (fun (body_entry_point,(eval_holes_fns,ext_holes)) ->
                  body_entry_point.fragment_code None eval_holes_fns ext_holes
               )
           in
           (* This gives us the case expressions we needed to build the match
              expression. *)
           let cases =
             patterns
             |> List.combine guards
             |> List.combine case_exprs
             |> List.map
               (fun (case_expr, (guard, pattern)) ->
                  { pc_lhs = pattern;
                    pc_guard = guard;
                    pc_rhs = case_expr
                  }
               )
           in
           { pexp_desc = Pexp_match(input_expr, cases);
             pexp_loc = loc;
             pexp_attributes = attributes
           }
        )
    }
  in
  (* Now we need to define the exit points for the overall match group we're
     building. *)
  let match_exits =
    (* Include the exit points for each case. *)
    bodies
    |> List.map (fun body -> body.fg_exits)
    |> List.fold_left Fragment_uid_set.union Fragment_uid_set.empty
    (* But if any case's entry matches its exit, then that case was a singleton
       fragment group.  That means that its expression will treat this new
       match expression as its exit.  So search through the exit UIDs and replace
       occurrences of any of these case's entry UIDs with the match fragment's
       UID. *)
    |> Fragment_uid_set.map
      (let case_uids =
         bodies
         |> List.map (fun body -> body.fg_entry)
         |> Fragment_uid_set.of_list
       in
       fun uid ->
         if Fragment_uid_set.mem uid case_uids then match_uid else uid
      )
  in
  (* Now we have the pieces to build the group for the match.  This group will
     still be open on the input side as we still haven't connected the group
     which defines the match subject. *)
  let match_group =
    { fg_graph =
        (
          Fragment_uid_map.add match_uid match_fragment @@
          let case_groups_without_entry =
            bodies
            |> List.map (fun b -> Fragment_uid_map.remove b.fg_entry b.fg_graph)
          in
          List.fold_left
            merge_fragment_graphs
            Fragment_uid_map.empty
            case_groups_without_entry
        );
      fg_loc = loc;
      fg_entry = match_uid;
      fg_exits = match_exits
    }
  in
  (* Now we can finally merge in the match subject. *)
  return @@ connect_dataflow loc g match_group




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
    let%bind uid = fresh_uid () in
    let constructor_fragment =
      { fragment_uid = uid;
        fragment_loc = loc;
        fragment_free_variables = Var_set.empty;
        fragment_input_hole = Some { inhd_loc = loc };
        fragment_evaluation_holes =
          [ { evhd_loc = loc;
              evhd_target_fragment = None;
              evhd_bound_variables = Var_map.empty;
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
             let e =
               { pexp_desc = Pexp_construct(name, Some input_expr);
                 pexp_loc = loc;
                 pexp_attributes = attributes;
               }
             in
             f e
          )
      }
    in
    let constructor_group =
      { fg_graph = Fragment_uid_map.singleton uid constructor_fragment;
        fg_loc = loc;
        fg_entry = uid;
        fg_exits = Fragment_uid_set.singleton uid;
      }
    in
    return @@ connect_dataflow loc g constructor_group




and fragment_ifthenelse
    (loc : Location.t) (attributes : attributes)
    (g1 : fragment_group) (g2 : fragment_group) (g3 : fragment_group)
  : fragment_group m =
  (* We simply need to join the graphs together.  The interesting work is to
     connect control flow between the groups:
        * The exit points of the condition group must flow into the entry of
          a new if-then-else group.
        * The if-then-else expression in the if-then-else group should
          incorporate the entry fragments of each of the then and else groups
          (to prevent unnecessary jumping).  The exit points of the
          if-then-else group are the exit points of the then and else groups.
        * The entry point of the condition group remains unchanged.
     Note that, if g2 and g3 are pure, this algorithm naturally combines them
     into one pure group.
  *)
  let%bind ifthenelse_uid = fresh_uid () in
  let g2_entry = Fragment_uid_map.find g2.fg_entry g2.fg_graph in
  let g3_entry = Fragment_uid_map.find g3.fg_entry g3.fg_graph in
  let ifthenelse_eval_holes =
    g2_entry.fragment_evaluation_holes @ g3_entry.fragment_evaluation_holes
  in
  let ifthenelse_ext_holes =
    g2_entry.fragment_extension_holes @ g3_entry.fragment_extension_holes
  in
  let ifthenelse_fragment =
    { fragment_uid = ifthenelse_uid;
      fragment_loc = loc;
      fragment_free_variables =
        Var_set.union
          g2_entry.fragment_free_variables g3_entry.fragment_free_variables;
      fragment_input_hole = Some { inhd_loc = loc };
      fragment_evaluation_holes = ifthenelse_eval_holes;
      fragment_extension_holes = ifthenelse_ext_holes;
      fragment_code =
        (fun input_expr_opt eval_holes_fns ext_holes_exprs ->
           let input_expr =
             assert_yes_input_expr ifthenelse_uid input_expr_opt
           in
           assert_evaluation_hole_function_count
             ifthenelse_uid (List.length ifthenelse_eval_holes)
             eval_holes_fns;
           assert_extension_hole_expression_count
             ifthenelse_uid (List.length ifthenelse_ext_holes)
             ext_holes_exprs;
           let then_eval_hole_fns, else_eval_hole_fns =
             List.takedrop (List.length g2_entry.fragment_evaluation_holes)
               eval_holes_fns
           in
           let then_ext_hole_exprs, else_ext_hole_exprs =
             List.takedrop (List.length g2_entry.fragment_extension_holes)
               ext_holes_exprs
           in
           let then_expr =
             g2_entry.fragment_code
               None then_eval_hole_fns then_ext_hole_exprs
           in
           let else_expr =
             g3_entry.fragment_code
               None else_eval_hole_fns else_ext_hole_exprs
           in
           { pexp_desc = Pexp_ifthenelse(input_expr, then_expr, Some else_expr);
             pexp_loc = loc;
             pexp_attributes = attributes
           }
        )
    }
  in
  let ifthenelse_exits =
    (* Include the exit points for both the then and else groups. *)
    g2.fg_exits
    |> Fragment_uid_set.union g3.fg_exits
    (* But either group's entry matches its exit, then it was a singleton
       fragment group.  That means that its expression will treat this new
       ifthenelse fragment as an exit.  So search through the exit UIDs and
       replace occurrences of the then and else entry UIDs with the ifthenelse
       fragment's UID. *)
    |> Fragment_uid_set.map
      (fun uid ->
         if uid = g2.fg_entry || uid = g3.fg_entry then ifthenelse_uid else uid)
  in
  let ifthenelse_group =
    { fg_graph =
        Fragment_uid_map.add ifthenelse_uid ifthenelse_fragment @@
        merge_fragment_graphs
          (Fragment_uid_map.remove g2.fg_entry g2.fg_graph)
          (Fragment_uid_map.remove g3.fg_entry g3.fg_graph);
      fg_loc = loc;
      fg_entry = ifthenelse_uid;
      fg_exits = ifthenelse_exits
    }
  in
  return @@ connect_dataflow loc g1 ifthenelse_group




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
;;
