open Batteries;;
open Jhupllib;;

open Location;;
open Parsetree;;

module String_value = struct
  type t = string;;
  let pp = Format.pp_print_string;;
end;;

module Tvar_set = struct
  module S = Set.Make(struct
      type t = string
      let compare = String.compare
    end);;
  include S;;
  include Pp_utils.Set_pp(S)(String_value);;
end;;

let rec tvars_of_type (t : core_type) : Tvar_set.t =
  match t.ptyp_desc with
  | Ptyp_any -> Tvar_set.empty
  | Ptyp_var s -> Tvar_set.singleton s
  | Ptyp_arrow(_,t1,t2) -> Tvar_set.union (tvars_of_type t1) (tvars_of_type t2)
  | Ptyp_tuple ts
  | Ptyp_constr(_,ts) ->
    List.fold_left Tvar_set.union Tvar_set.empty @@
    List.map tvars_of_type ts
  | Ptyp_object _ ->
    raise @@ Utils.Not_yet_implemented "tvars_of_type: Ptyp_object"
  | Ptyp_class _ ->
    raise @@ Utils.Not_yet_implemented "tvars_of_type: Ptyp_class"
  | Ptyp_alias(t,_) -> tvars_of_type t
  | Ptyp_variant _ ->
    raise @@ Utils.Not_yet_implemented "tvars_of_type: Ptyp_variant"
  | Ptyp_poly(vars,t) ->
    Tvar_set.union (tvars_of_type t) @@
    (vars |> List.enum |> Enum.map (fun x -> x.txt) |> Tvar_set.of_enum)
  | Ptyp_package _ ->
    raise @@ Utils.Not_yet_implemented "tvars_of_type: Ptyp_package"
  | Ptyp_extension _ ->
    raise @@ Utils.Not_yet_implemented "tvars_of_type: Ptyp_extension"
;;
