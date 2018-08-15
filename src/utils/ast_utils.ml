open Asttypes;;
open Parsetree;;

let expression_pseudo_tuple (loc : Location.t) (exprs : expression list)
  : expression =
  match exprs with
  | [] -> [%expr ()][@metaloc loc]
  | [expr] -> expr
  | _ ->
    { pexp_desc = Pexp_tuple(exprs);
      pexp_loc = loc;
      pexp_attributes = [];
    }
;;

let pattern_pseudo_tuple (loc : Location.t) (pats : pattern list)
  : pattern =
  match pats with
  | [] -> [%pat? ()][@metaloc loc]
  | [pat] -> pat
  | _ ->
    { ppat_desc = Ppat_tuple(pats);
      ppat_loc = loc;
      ppat_attributes = [];
    }
;;
