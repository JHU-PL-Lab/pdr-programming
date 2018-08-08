open Batteries;;
open Jhupllib;;

open Asttypes;;
open Parsetree;;

type fresh_variable_context =
  { fvc_counter : int ref;
    fvc_prefix : string }
;;

let new_fresh_variable_context ?prefix:(prefix="__var_") () =
  { fvc_counter = ref 0;
    fvc_prefix = prefix }
;;

let fresh_variable_name fvc =
  let n = !(fvc.fvc_counter) in
  fvc.fvc_counter := n + 1;
  fvc.fvc_prefix ^ string_of_int n
;;

module Longident_value =
struct
  type t = Longident.t
  let rec compare (x : t) (y : t) =
    match x,y with
    | Longident.Lident xs, Longident.Lident ys -> String.compare xs ys
    | Longident.Lident _, Longident.Ldot _ -> -1
    | Longident.Lident _, Longident.Lapply _ -> -1
    | Longident.Ldot _, Longident.Lident _ -> 1
    | Longident.Ldot(xr,xs), Longident.Ldot(yr,ys) ->
      let c = compare xr yr in
      if c = 0 then String.compare xs ys else c
    | Longident.Ldot _, Longident.Lapply _ -> -1
    | Longident.Lapply _, Longident.Lident _ -> 1
    | Longident.Lapply _, Longident.Ldot _ -> 1
    | Longident.Lapply(x1,x2), Longident.Lapply(y1,y2) ->
      let c = compare x1 y1 in
      if c = 0 then compare x2 y2 else c
  ;;
  let equal (x : t) (y : t ) =
    compare x y = 0
  ;;
  let pp formatter (ident : t) =
    Format.pp_print_string formatter @@
    String.join "." @@
    Longident.flatten ident
  ;;
  let show = Pp_utils.pp_to_string pp;;
end;;

module Var_set =
struct
  module Impl = Set.Make(Longident_value);;
  include Impl
  include Pp_utils.Set_pp(Impl)(Longident_value);;
  let unions sets =
    List.fold_left union empty sets
end;;

module Var_map =
struct
  module Impl = Map.Make(Longident_value);;
  include Impl
  include Pp_utils.Map_pp(Impl)(Longident_value);;
  let disjoint_union (a : 'a t) (b : 'a t) : 'a t =
    merge
      (fun _ value1o value2o ->
         match value1o, value2o with
         | Some value1, None -> Some value1
         | None, Some value2 -> Some value2
         | None, None -> None
         | Some _, Some _ ->
           raise @@ Invalid_argument
             "Attempted to disjoint union two non-disjoint variable maps"
      )
      a b
  ;;
  let disjoint_unions (xs : 'a t list) : 'a t =
    List.fold_left disjoint_union empty xs
  ;;
  let union_left (a : 'a t) (b : 'a t) : 'a t =
    merge
      (fun _ value1o value2o ->
         match value1o, value2o with
         | Some value1, _ -> Some value1
         | None, Some value2 -> Some value2
         | None, None -> None
      )
      a b
  ;;
end;;

exception Multiply_bound_variable of Longident.t;;

let rec bound_pattern_vars (p : pattern) : Var_set.t =
  match p.ppat_desc with
  | Parsetree.Ppat_any -> Var_set.empty
  | Parsetree.Ppat_var x -> Var_set.singleton @@ Longident.Lident(x.txt)
  | Parsetree.Ppat_alias (p',x) -> Var_set.add (Longident.Lident(x.txt)) (bound_pattern_vars p')
  | Parsetree.Ppat_constant _ -> Var_set.empty
  | Parsetree.Ppat_interval (_,_) -> Var_set.empty
  | Parsetree.Ppat_tuple ps ->
    Var_set.unions @@ List.map bound_pattern_vars ps
  | Parsetree.Ppat_construct (_,p_opt) ->
    Option.default Var_set.empty @@ Option.map bound_pattern_vars p_opt
  | Parsetree.Ppat_variant (_,p_opt) ->
    Option.default Var_set.empty @@ Option.map bound_pattern_vars p_opt
  | Parsetree.Ppat_record (rps,_) ->
    Var_set.unions @@ List.map bound_pattern_vars @@ List.map snd rps
  | Parsetree.Ppat_array ps ->
    Var_set.unions @@ List.map bound_pattern_vars ps
  | Parsetree.Ppat_or (p1,p2) ->
    Var_set.inter (bound_pattern_vars p1) (bound_pattern_vars p2)
  | Parsetree.Ppat_constraint (p',_) -> bound_pattern_vars p'
  | Parsetree.Ppat_type _ ->
    raise @@ Utils.Not_yet_implemented "bound_pattern_vars: Ppat_type"
  | Parsetree.Ppat_lazy p' -> bound_pattern_vars p'
  | Parsetree.Ppat_unpack m -> Var_set.singleton @@ Longident.Lident(m.txt)
  | Parsetree.Ppat_exception p' -> bound_pattern_vars p'
  | Parsetree.Ppat_extension _ -> Var_set.empty
  | Parsetree.Ppat_open (_,_) ->
    raise @@ Utils.Not_yet_implemented "bound_pattern_vars: Ppat_open"
;;

let rec bound_pattern_vars_with_type
    (p : pattern)
  : core_type option Var_map.t =
  let disjoint_union
      (a : core_type option Var_map.t) (b : core_type option Var_map.t)
    : core_type option Var_map.t =
    Var_map.merge
      (fun k value1o value2o ->
         match value1o, value2o with
         | Some value1, None -> Some value1
         | None, Some value2 -> Some value2
         | None, None -> None
         | Some value1, Some value2 ->
           if value1 = value2 then Some value1 else
             raise @@ Multiply_bound_variable k
      )
      a b
  in
  let disjoint_unions
      (xs : core_type option Var_map.t list)
    : core_type option Var_map.t =
    List.fold_left disjoint_union Var_map.empty xs
  in
  let intersection
      (a : core_type option Var_map.t) (b : core_type option Var_map.t)
    : core_type option Var_map.t =
    Var_map.merge
      (fun k value1o value2o ->
         match value1o, value2o with
         | Some value1, Some value2 ->
           if value1 = value2 then Some value1 else
             raise @@ Multiply_bound_variable k
         | _, _ -> None
      )
      a b
  in
  match p.ppat_desc with
  | Parsetree.Ppat_any -> Var_map.empty
  | Parsetree.Ppat_var x -> Var_map.singleton (Longident.Lident(x.txt)) None
  | Parsetree.Ppat_alias (p',x) ->
    Var_map.add (Longident.Lident(x.txt)) None (bound_pattern_vars_with_type p')
  | Parsetree.Ppat_constant _ -> Var_map.empty
  | Parsetree.Ppat_interval (_,_) -> Var_map.empty
  | Parsetree.Ppat_tuple ps ->
    disjoint_unions @@ List.map bound_pattern_vars_with_type ps
  | Parsetree.Ppat_construct (_,p_opt) ->
    Option.default Var_map.empty @@
    Option.map bound_pattern_vars_with_type p_opt
  | Parsetree.Ppat_variant (_,p_opt) ->
    Option.default Var_map.empty @@
    Option.map bound_pattern_vars_with_type p_opt
  | Parsetree.Ppat_record (rps,_) ->
    disjoint_unions @@ List.map bound_pattern_vars_with_type @@ List.map snd rps
  | Parsetree.Ppat_array ps ->
    disjoint_unions @@ List.map bound_pattern_vars_with_type ps
  | Parsetree.Ppat_or (p1,p2) ->
    intersection
      (bound_pattern_vars_with_type p1) (bound_pattern_vars_with_type p2)
  | Parsetree.Ppat_constraint (p',t) ->
    begin
      match p'.ppat_desc with
      | Parsetree.Ppat_var x ->
        Var_map.singleton (Longident.Lident(x.txt)) (Some t)
      | _ ->
        bound_pattern_vars_with_type p'
    end
  | Parsetree.Ppat_type _ ->
    raise @@ Utils.Not_yet_implemented "bound_pattern_vars_with_type: Ppat_type"
  | Parsetree.Ppat_lazy p' ->
    bound_pattern_vars_with_type p'
  | Parsetree.Ppat_unpack m ->
    Var_map.singleton (Longident.Lident(m.txt)) None
  | Parsetree.Ppat_exception p' -> bound_pattern_vars_with_type p'
  | Parsetree.Ppat_extension _ -> Var_map.empty
  | Parsetree.Ppat_open (_,_) ->
    raise @@ Utils.Not_yet_implemented "bound_pattern_vars_with_type: Ppat_open"
;;

let rec free_expr_vars (e : expression) : Var_set.t =
  match e.pexp_desc with
  | Parsetree.Pexp_ident x -> Var_set.singleton @@ x.txt
  | Parsetree.Pexp_constant _ -> Var_set.empty
  | Parsetree.Pexp_let (rec_flag,bindings,body) ->
    let bound =
      Var_set.unions @@
      List.map bound_pattern_vars @@ List.map (fun vb -> vb.pvb_pat) bindings
    in
    let free_in_binding_exprs =
      let initially_free =
        Var_set.unions @@
        List.map free_expr_vars @@ List.map (fun vb -> vb.pvb_expr) bindings
      in
      match rec_flag with
      | Recursive -> Var_set.diff initially_free bound
      | Nonrecursive -> initially_free
    in
    let free_in_body = free_expr_vars body in
    Var_set.union (Var_set.diff free_in_body bound) free_in_binding_exprs
  | Parsetree.Pexp_function cases ->
    Var_set.unions @@ List.map free_case_vars cases
  | Parsetree.Pexp_fun (_, default_expr, pattern, body) ->
    let default_expr_free_vars =
      Option.map_default free_expr_vars Var_set.empty default_expr
    in
    let pattern_bound_vars = bound_pattern_vars pattern in
    let body_free_vars = free_expr_vars body in
    Var_set.union default_expr_free_vars @@
    Var_set.diff body_free_vars pattern_bound_vars
  | Parsetree.Pexp_apply (func_expr,args) ->
    Var_set.union (free_expr_vars func_expr) @@
    Var_set.unions @@ List.map free_expr_vars @@ List.map snd args
  | Parsetree.Pexp_match (subject_expr, cases) ->
    Var_set.union (free_expr_vars subject_expr) @@
    Var_set.unions @@ List.map free_case_vars cases
  | Parsetree.Pexp_try (try_expr,cases) ->
    Var_set.union (free_expr_vars try_expr) @@
    Var_set.unions @@ List.map free_case_vars cases
  | Parsetree.Pexp_tuple exprs ->
    Var_set.unions @@ List.map free_expr_vars exprs
  | Parsetree.Pexp_construct (_,e') ->
    Option.map_default free_expr_vars Var_set.empty e'
  | Parsetree.Pexp_variant (_,e') ->
    Option.map_default free_expr_vars Var_set.empty e'
  | Parsetree.Pexp_record (terms,with_expr_opt) ->
    Var_set.union
      (Option.map_default free_expr_vars Var_set.empty with_expr_opt) @@
    Var_set.unions @@ List.map free_expr_vars @@ List.map snd terms
  | Parsetree.Pexp_field (e',_) -> free_expr_vars e'
  | Parsetree.Pexp_setfield (e1,_,e2) ->
    Var_set.union (free_expr_vars e1) (free_expr_vars e2)
  | Parsetree.Pexp_array exprs ->
    Var_set.unions @@ List.map free_expr_vars exprs
  | Parsetree.Pexp_ifthenelse (e1,e2,e3) ->
    Var_set.union (free_expr_vars e1) @@
    Var_set.union (free_expr_vars e2) @@
    Option.map_default free_expr_vars Var_set.empty e3
  | Parsetree.Pexp_sequence (e1,e2) ->
    Var_set.union (free_expr_vars e1) (free_expr_vars e2)
  | Parsetree.Pexp_while (e1,e2) ->
    Var_set.union (free_expr_vars e1) (free_expr_vars e2)
  | Parsetree.Pexp_for (pattern,e1,e2,_,e3) ->
    Var_set.unions
      [ free_expr_vars e1;
        free_expr_vars e2;
        Var_set.diff (bound_pattern_vars pattern) @@ free_expr_vars e3 ]
  | Parsetree.Pexp_constraint (e',_) -> free_expr_vars e'
  | Parsetree.Pexp_coerce (e',_,_) -> free_expr_vars e'
  | Parsetree.Pexp_send (e',_) -> free_expr_vars e'
  | Parsetree.Pexp_new _ -> Var_set.empty
  | Parsetree.Pexp_setinstvar (_,_) ->
    raise @@ Utils.Not_yet_implemented "free_expr_vars: Pexp_setinstvar"
  | Parsetree.Pexp_override _ ->
    raise @@ Utils.Not_yet_implemented "free_expr_vars: Pexp_override"
  | Parsetree.Pexp_letmodule (_,_,_) ->
    raise @@ Utils.Not_yet_implemented "free_expr_vars: Pexp_letmodule"
  | Parsetree.Pexp_letexception (_,_) ->
    raise @@ Utils.Not_yet_implemented "free_expr_vars: Pexp_letexception"
  | Parsetree.Pexp_assert e' -> free_expr_vars e'
  | Parsetree.Pexp_lazy e' -> free_expr_vars e'
  | Parsetree.Pexp_poly (_,_) ->
    raise @@ Utils.Not_yet_implemented "free_expr_vars: Pexp_poly"
  | Parsetree.Pexp_object _ ->
    raise @@ Utils.Not_yet_implemented "free_expr_vars: Pexp_object"
  | Parsetree.Pexp_newtype (_,_) ->
    raise @@ Utils.Not_yet_implemented "free_expr_vars: Pexp_newtype"
  | Parsetree.Pexp_pack _ -> Var_set.empty
  | Parsetree.Pexp_open (_,_,_) ->
    raise @@ Utils.Not_yet_implemented "free_expr_vars: Pexp_open"
  | Parsetree.Pexp_extension _ -> Var_set.empty
  | Parsetree.Pexp_unreachable  -> Var_set.empty

and free_case_vars case =
  Var_set.diff
    (Var_set.union
       (free_expr_vars case.pc_rhs)
       (Option.map_default free_expr_vars Var_set.empty case.pc_guard))
    (bound_pattern_vars case.pc_lhs)
;;
