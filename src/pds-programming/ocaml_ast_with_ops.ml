(**
   This module contains utility functions for the types in Parsetree.
*)

open Parsetree;;

module Location =
struct
  include Location;;
  let equal x y = true;;
  let compare x y = 0;;
  let pp _ _ = ();;
end;;

module Longident =
struct
  type t = [%import: Longident.t] [@@deriving eq, ord, show];;
end;;

module Asttypes =
struct
  type 'a loc = [%import: 'a Asttypes.loc];;
  let equal_loc eq x y = eq x.Asttypes.txt y.Asttypes.txt;;
  let compare_loc cmp x y = cmp x.Asttypes.txt y.Asttypes.txt;;
  let pp_loc pp fmt x = pp fmt x.Asttypes.txt;;

  type rec_flag = [%import: Asttypes.rec_flag] [@@deriving eq, ord, show];;
  type direction_flag = [%import: Asttypes.direction_flag] [@@deriving eq, ord, show];;
  type private_flag = [%import: Asttypes.private_flag] [@@deriving eq, ord, show];;
  type mutable_flag = [%import: Asttypes.mutable_flag] [@@deriving eq, ord, show];;
  type virtual_flag = [%import: Asttypes.virtual_flag] [@@deriving eq, ord, show];;
  type override_flag = [%import: Asttypes.override_flag] [@@deriving eq, ord, show];;
  type closed_flag = [%import: Asttypes.closed_flag] [@@deriving eq, ord, show];;
  type label = [%import: Asttypes.label] [@@deriving eq, ord, show];;
  type arg_label = [%import: Asttypes.arg_label] [@@deriving eq, ord, show];;
  type constant = [%import: Asttypes.constant] [@@deriving eq, ord, show];;
  type variance = [%import: Asttypes.variance] [@@deriving eq, ord, show];;
end;;

type attribute =
  [%import: Parsetree.attribute]
[@@deriving eq, ord, show]

and attributes =
    [%import: Parsetree.attributes]
[@@deriving eq, ord, show]

and case =
    [%import: Parsetree.case]
[@@deriving eq, ord, show]

and class_declaration =
    [%import: Parsetree.class_declaration]
[@@deriving eq, ord, show]

and class_description =
    [%import: Parsetree.class_description]
[@@deriving eq, ord, show]

and class_expr =
    [%import: Parsetree.class_expr]
[@@deriving eq, ord, show]

and class_expr_desc =
    [%import: Parsetree.class_expr_desc]
[@@deriving eq, ord, show]

and class_field =
    [%import: Parsetree.class_field]
[@@deriving eq, ord, show]

and class_field_desc =
    [%import: Parsetree.class_field_desc]
[@@deriving eq, ord, show]

and class_field_kind =
    [%import: Parsetree.class_field_kind]
[@@deriving eq, ord, show]

and 'a class_infos =
    [%import: 'a Parsetree.class_infos]
[@@deriving eq, ord, show]

and class_signature =
    [%import: Parsetree.class_signature]
[@@deriving eq, ord, show]

and class_structure =
    [%import: Parsetree.class_structure]
[@@deriving eq, ord, show]

and class_type =
    [%import: Parsetree.class_type]
[@@deriving eq, ord, show]

and class_type_declaration =
    [%import: Parsetree.class_type_declaration]
[@@deriving eq, ord, show]

and class_type_desc =
    [%import: Parsetree.class_type_desc]
[@@deriving eq, ord, show]

and class_type_field =
    [%import: Parsetree.class_type_field]
[@@deriving eq, ord, show]

and class_type_field_desc =
    [%import: Parsetree.class_type_field_desc]
[@@deriving eq, ord, show]

and constant =
    [%import: Parsetree.constant]
[@@deriving eq, ord, show]

and constructor_arguments =
    [%import: Parsetree.constructor_arguments]
[@@deriving eq, ord, show]

and constructor_declaration =
    [%import: Parsetree.constructor_declaration]
[@@deriving eq, ord, show]

and core_type =
    [%import: Parsetree.core_type]
[@@deriving eq, ord, show]

and core_type_desc =
    [%import: Parsetree.core_type_desc]
[@@deriving eq, ord, show]

and expression =
    [%import: Parsetree.expression]
[@@deriving eq, ord, show]

and expression_desc =
    [%import: Parsetree.expression_desc]
[@@deriving eq, ord, show]

and extension =
    [%import: Parsetree.extension]
[@@deriving eq, ord, show]

and extension_constructor =
    [%import: Parsetree.extension_constructor]
[@@deriving eq, ord, show]

and extension_constructor_kind =
    [%import: Parsetree.extension_constructor_kind]
[@@deriving eq, ord, show]

and include_declaration =
    [%import: Parsetree.include_declaration]
[@@deriving eq, ord, show]

and include_description =
    [%import: Parsetree.include_description]
[@@deriving eq, ord, show]

and 'a include_infos =
    [%import: 'a Parsetree.include_infos]
[@@deriving eq, ord, show]

and label_declaration =
    [%import: Parsetree.label_declaration]
[@@deriving eq, ord, show]

and module_binding =
    [%import: Parsetree.module_binding]
[@@deriving eq, ord, show]

and module_declaration =
    [%import: Parsetree.module_declaration]
[@@deriving eq, ord, show]

and module_expr =
    [%import: Parsetree.module_expr]
[@@deriving eq, ord, show]

and module_expr_desc =
    [%import: Parsetree.module_expr_desc]
[@@deriving eq, ord, show]

and module_type =
    [%import: Parsetree.module_type]
[@@deriving eq, ord, show]

and module_type_declaration =
    [%import: Parsetree.module_type_declaration]
[@@deriving eq, ord, show]

and module_type_desc =
    [%import: Parsetree.module_type_desc]
[@@deriving eq, ord, show]

and open_description =
    [%import: Parsetree.open_description]
[@@deriving eq, ord, show]

and package_type =
    [%import: Parsetree.package_type]
[@@deriving eq, ord, show]

and pattern =
    [%import: Parsetree.pattern]
[@@deriving eq, ord, show]

and pattern_desc =
    [%import: Parsetree.pattern_desc]
[@@deriving eq, ord, show]

and payload =
    [%import: Parsetree.payload]
[@@deriving eq, ord, show]

and row_field =
    [%import: Parsetree.row_field]
[@@deriving eq, ord, show]

and signature =
    [%import: Parsetree.signature]
[@@deriving eq, ord, show]

and signature_item =
    [%import: Parsetree.signature_item]
[@@deriving eq, ord, show]

and signature_item_desc =
    [%import: Parsetree.signature_item_desc]
[@@deriving eq, ord, show]

and structure =
    [%import: Parsetree.structure]
[@@deriving eq, ord, show]

and structure_item =
    [%import: Parsetree.structure_item]
[@@deriving eq, ord, show]

and structure_item_desc =
    [%import: Parsetree.structure_item_desc]
[@@deriving eq, ord, show]

and type_declaration =
    [%import: Parsetree.type_declaration]
[@@deriving eq, ord, show]

and type_extension =
    [%import: Parsetree.type_extension]
[@@deriving eq, ord, show]

and type_kind =
    [%import: Parsetree.type_kind]
[@@deriving eq, ord, show]

and value_binding =
    [%import: Parsetree.value_binding]
[@@deriving eq, ord, show]

and value_description =
    [%import: Parsetree.value_description]
[@@deriving eq, ord, show]

and with_constraint =
    [%import: Parsetree.with_constraint]
[@@deriving eq, ord, show]
;;
