open Location;;
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

let error_as_type (loc : Location.t) (message : string) : core_type =
  { ptyp_desc =
      Ptyp_extension(
        mkloc "ocaml.error" loc,
        PStr([
            { pstr_desc =
                Pstr_eval(
                  { pexp_desc = Pexp_constant(Pconst_string(message,None));
                    pexp_loc = loc;
                    pexp_attributes = [];
                  },
                  []
                );
              pstr_loc = loc;
            }
          ])
      );
    ptyp_loc = loc;
    ptyp_attributes = [];
  }
;;
