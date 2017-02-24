open Batteries;;
open Jhupllib;;

open Parsetree;;
open Asttypes;;
open Longident;;
open Ast_helper;;

(*TODO: what is this*)
(* let pp_expression = Pprintast.expression;; *)
let pp_expression fmt e =
  Format.pp_print_text fmt "<<";
  Pprintast.expression fmt e;
  Format.pp_print_text fmt ">>";
;;
let equal_expression = Ocaml_ast_without_location.equal_expression;;
let compare_expression = Ocaml_ast_without_location.compare_expression;;

(* let pp_pattern = Pprintast.pattern;; *)
let pp_pattern fmt p =
  Format.pp_print_text fmt "<<";
  Pprintast.pattern fmt p;
  Format.pp_print_text fmt ">>";
;;
let equal_pattern = Ocaml_ast_without_location.equal_pattern;;
let compare_pattern = Ocaml_ast_without_location.compare_pattern;;

exception Unflattened_extension;;

(*TODO: I know what locwrap is but what are we doing here/do I need to know? *)
let locwrap (type a) (x : a) : a Asttypes.loc =
  {txt = x;
   loc = !default_loc}
;;

module String_ord =
struct
  type t = string
  let compare x y = Pervasives.compare x y
end;;

module String_set =
  Set.Make (String_ord);;

(*for printing out string sets*)
let show_stringset s =
  Pp_utils.pp_to_string (Pp_utils.pp_set Format.pp_print_string String_set.enum) s;;

(*retrieves all of the variables in a given pattern, p, and returns their
  names as a string set. For use in freevars.*)
let rec varmatch p =
  let {ppat_desc; _ } = p in
  match ppat_desc with
  | Ppat_any -> String_set.empty
  | Ppat_var s -> String_set.singleton s.txt
  | Ppat_alias (pat, s) -> String_set.union (varmatch pat) (String_set.singleton s.txt)
  | Ppat_constant _ -> String_set.empty
  | Ppat_interval _ -> String_set.empty
  | Ppat_tuple l -> let mapped_l = List.map varmatch l in
    List.fold_left String_set.union String_set.empty mapped_l
  | Ppat_construct (_, pat) ->
    begin match pat with
    | None -> String_set.empty
    | Some pat' -> varmatch pat'
    end
  | Ppat_variant (_, pat) ->
    begin match pat with
      | None -> String_set.empty
      | Some pat' -> varmatch pat'
    end
  | Ppat_record (l, _) -> let mapped_l =
                               let patlist = List.map (fun (_,y) -> y) l
                               in List.map varmatch patlist
    in List.fold_left String_set.union String_set.empty mapped_l
  | Ppat_array l -> let mapped_l = List.map varmatch l in
    List.fold_left String_set.union String_set.empty mapped_l
  | Ppat_or (p1, p2) -> String_set.inter (varmatch p1) (varmatch p2) (*TODO: what is this*)
  | Ppat_constraint (p1, _) -> varmatch p1
  | Ppat_type _ -> String_set.empty
  | Ppat_lazy p1 -> varmatch p1
  | Ppat_unpack _ -> raise (Utils.Not_yet_implemented "varmatch Ppat_unpack")
  | Ppat_exception pat -> varmatch pat
  | Ppat_extension _ -> raise Unflattened_extension;; (*TODO: how does this work?*)

(*determines free variables in a given expression. takes bound, a string set of
  variables that are already bound, and expr, an expression. returns a string
  set of names of bound variables. Uses varmatch. For use in A-translator.*)
let rec freevars bound expr =
  let {pexp_desc; _} = expr in
  match pexp_desc with
  (*expression is a variable*)
  | Pexp_ident s -> begin
      match s.txt with
      | Lident l -> if String_set.mem l bound
        then (*if variable is already in set of bound variables, there are
             no unbound variables in this expression.*)
          String_set.empty
        else
          String_set.singleton l
      | Ldot _ -> raise (Utils.Not_yet_implemented "freevars Pexp_ident (Longident of Ldot)")
      | Lapply _ -> raise (Utils.Not_yet_implemented "freevars Pexp_ident (Longident of Lapply)")
    end
  | Pexp_constant _ -> String_set.empty
  (*expression is a let expression; TODO: come back to this.*)
  | Pexp_let (rflag, vb_list, e) ->
    let getvbvars vb = varmatch vb.pvb_pat
    in let vbvarlist = List.map getvbvars vb_list
    in let vbvars = List.fold_left String_set.union String_set.empty vbvarlist
    in let allvars = String_set.union vbvars bound
    in let vbunbound =
         if rflag = Nonrecursive
         then
           (let vbunboundlist = List.map (fun vb -> freevars bound vb.pvb_expr) vb_list
            in List.fold_left String_set.union String_set.empty vbunboundlist)
         else
           (let vbunboundlist = List.map (fun vb -> freevars allvars vb.pvb_expr) vb_list
            in List.fold_left String_set.union String_set.empty vbunboundlist)
    in let exprunbound = freevars allvars e
    in String_set.union vbunbound exprunbound
  | Pexp_function case_list -> let cbound c = String_set.union bound (varmatch c.pc_lhs)
    in let cvars c = (match c.pc_guard with
        | None -> freevars (cbound c) c.pc_rhs
        | Some guard -> String_set.union (freevars (cbound c) c.pc_rhs) (freevars (cbound c) guard))
    in let cfreelist = List.map cvars case_list
    in List.fold_left String_set.union String_set.empty cfreelist
  | Pexp_fun (_, e1_option, p, e2) -> (*unsure if this one is correct*)
    let bvars = String_set.union (varmatch p) bound in
    let e2unbound = freevars bvars e2 in
    (match e1_option with
     | None -> e2unbound
     | Some e1 -> String_set.union e2unbound (freevars bound e1))
  | Pexp_apply (e1, l) ->
    let unboundlist = List.map (function (_, e) -> freevars bound e) l in
    let unboundset = List.fold_left String_set.union String_set.empty unboundlist in
    String_set.union (freevars bound e1) unboundset
  | Pexp_match (e, case_list) ->
    let exprbound c = String_set.union bound (varmatch c.pc_lhs) in
    let exprunbound c = freevars (exprbound c) c.pc_rhs in
    let caseunbound c = (match c.pc_guard with
        | None -> exprunbound c
        | Some guard -> String_set.union (exprunbound c) (freevars (exprbound c) guard)) in
    let caseunboundlist = List.map caseunbound case_list in
    let unbound = List.fold_left String_set.union String_set.empty caseunboundlist in
    String_set.union (freevars bound e) unbound
  | Pexp_try (e, case_list) ->
    let exprbound c = String_set.union bound (varmatch c.pc_lhs) in
    let exprunbound c = freevars (exprbound c) c.pc_rhs in
    let caseunbound c = (match c.pc_guard with
        | None -> exprunbound c
        | Some guard -> String_set.union (exprunbound c) (freevars (exprbound c) guard)) in
    let caseunboundlist = List.map caseunbound case_list in
    let unbound = List.fold_left String_set.union String_set.empty caseunboundlist in
    String_set.union (freevars bound e) unbound
  | Pexp_tuple l -> let mapped_l = List.map (freevars bound) l in
    List.fold_left String_set.union String_set.empty mapped_l
  | Pexp_construct (_, e_option) -> (match e_option with
      | None -> String_set.empty
      | Some e -> freevars bound e)
  | Pexp_variant (_, e_option) -> (match e_option with
      | None -> String_set.empty
      | Some e -> freevars bound e)
  | Pexp_record (l, e_option) ->
    let explist = List.map (function (_,e) -> freevars bound e) l in
    let exp_unbound = List.fold_left String_set.union String_set.empty explist
    in (match e_option with
        | None -> exp_unbound
        | Some e1 -> String_set.union (freevars bound e1) exp_unbound)
  | Pexp_field (e, _) -> freevars bound e
  | Pexp_setfield (e1, _, e2) -> String_set.union (freevars bound e1) (freevars bound e2)
  | Pexp_array l -> let mapped_l = List.map (freevars bound) l in
    List.fold_left String_set.union String_set.empty mapped_l
  | Pexp_ifthenelse (e1, e2, e3) ->
    let e1e2 = String_set.union (freevars bound e1) (freevars bound e2) in
    begin
      match e3 with
      | None -> e1e2
      | Some exp -> String_set.union (freevars bound exp) e1e2
  end
  | Pexp_sequence (e1, e2) -> String_set.union (freevars bound e1) (freevars bound e2)
  | Pexp_while (e1, e2) -> String_set.union (freevars bound e1) (freevars bound e2)
  | Pexp_for _ -> raise (Utils.Not_yet_implemented "freevars Pexp_for")
  | Pexp_constraint (e, _) -> freevars bound e
  | Pexp_coerce (e, _, _) -> freevars bound e
  | Pexp_send _ -> raise (Utils.Not_yet_implemented "freevars Pexp_send")
  | Pexp_new _ -> raise (Utils.Not_yet_implemented "freevars Pexp_new")
  | Pexp_setinstvar _ -> raise (Utils.Not_yet_implemented "freevars Pexp_setinstvar")
  | Pexp_override _ -> raise (Utils.Not_yet_implemented "freevars Pexp_override")
  | Pexp_letmodule _ -> raise (Utils.Not_yet_implemented "freevars Pexp_letmodule")
  | Pexp_assert e -> freevars bound e
  | Pexp_lazy e -> freevars bound e
  | Pexp_poly _ -> raise (Utils.Not_yet_implemented "freevars Pexp_poly")
  | Pexp_object _ -> raise (Utils.Not_yet_implemented "freevars Pexp_object")
  | Pexp_newtype _ -> raise (Utils.Not_yet_implemented "freevars Pexp_newtype")
  | Pexp_pack _ -> raise (Utils.Not_yet_implemented "freevars Pexp_pack")
  | Pexp_open _ -> raise (Utils.Not_yet_implemented "freevars Pexp_open")
  | Pexp_extension _ -> raise Unflattened_extension;;
