open Batteries;;
open Jhupllib;;

open Asttypes;;
open Location;;
open Parsetree;;

open Pdr_programming_continuation_extensions.Fragment_types;;
open Pdr_programming_utils.Big_variant;;
open Pdr_programming_utils.Type_utils;;
open Pdr_programming_utils.Variable_utils;;

open Flow_analysis;;

exception Unannotated_continuation_variable of Longident.t * Location.t;;

type continuation_type_spec =
  { cts_bvs : big_variant_spec;
    cts_uid_map : int Fragment_uid_map.t;
  }
;;

let _unident (x : Longident.t) : string =
  match x with
  | Lident s -> s
  | _ -> raise @@ Utils.Not_yet_implemented "_unident: non-Lident"
;;

let create_continuation_type_constructors
    (group : fragment_group)
  : constructor_declaration list * int Fragment_uid_map.t =
  (* Get all of the UIDs for which we need to make continuations.  We make a
     continuation for a fragment if it is the target of an extension hole.
     Whether a fragment is the target of an evaluation hole is irrelevant: if it
     is the target of an extension hole as well, a continuation is needed; if it
     is only the target of an evaluation hole, we need not construct a
     continuation value for it because it is executed immediately.
  *)
  let continuation_uids =
    group.fg_graph
    |> Fragment_uid_map.values
    |> Enum.map
      (fun fragment ->
         fragment.fragment_extension_holes
         |> List.enum
         |> Enum.map (fun exhd -> exhd.exhd_target_fragment)
      )
    |> Enum.concat
    |> Enum.filter_map identity
    |> Fragment_uid_set.of_enum (* eliminate duplicates *)
    |> Fragment_uid_set.enum
    |> List.of_enum
  in
  let uid_map =
    ( List.enum continuation_uids,
      0 --^ List.length continuation_uids
    )
    |> Enum.combine
    |> Fragment_uid_map.of_enum
  in
  let intermediate_var_map = Flow_analysis.determine_intermediates group in
  let constructors =
    continuation_uids
    |> List.enum
    |> Enum.map
      (fun uid ->
         let fragment = Fragment_uid_map.find uid group.fg_graph in
         let constructor_name =
           "Continuation_fragment_" ^ Fragment_uid.show fragment.fragment_uid
         in
         let intermediate_vars =
           Fragment_uid_map.find_default
             Flow_analysis.Intermediate_var_set.empty
             uid intermediate_var_map
         in
         let constructor_params =
           let external_binding_types : core_type Enum.t  =
             fragment.fragment_externally_bound_variables
             |> Var_map.values
             |> Enum.map
               (fun ebv ->
                  match ebv.ebv_type with
                  | Some typ -> typ
                  | None ->
                    raise @@
                    Unannotated_continuation_variable(
                      ebv.ebv_variable, ebv.ebv_bind_loc)
               )
           in
           let intermediate_variable_types : core_type Enum.t =
             intermediate_vars
             |> Flow_analysis.Intermediate_var_set.enum
             |> Enum.filter
               (* Throw away any intermediate variable which also appears in our
                  external binding set.  We already have a copy of that value
                  from our external binding, so there's no sense in capturing
                  another. *)
               (fun iv ->
                  let ebv_map = fragment.fragment_externally_bound_variables in
                  not @@
                  (Var_map.mem iv.iv_name ebv_map &&
                   Fragment_uid.equal
                     (Var_map.find iv.iv_name ebv_map).ebv_binder
                     iv.iv_binder
                  )
               )
             |> Enum.map
               (fun iv ->
                  match iv.iv_type with
                  | Some typ -> typ
                  | None ->
                    raise @@
                    Unannotated_continuation_variable(
                      iv.iv_name, iv.iv_bind_loc)
               )
           in
           let param_types =
             List.enum [external_binding_types;
                        intermediate_variable_types;
                       ]
             |> Enum.concat
             |> List.of_enum
           in
           (param_types : core_type list)
           (* Sometimes, type annotations are parsed as "Ptyp_poly" types with
              no polymorphic variables.  This clutters the AST and messes with
              testing, so let's remove them. *)
           |> List.map
             (fun typ ->
                match typ.ptyp_desc with
                | Ptyp_poly([], typ') -> typ'
                | _ -> typ
             )
         in
         { pcd_name = mkloc constructor_name fragment.fragment_loc;
           pcd_args = Pcstr_tuple constructor_params;
           pcd_res = None;
           pcd_loc = fragment.fragment_loc;
           pcd_attributes = [];
         }
      )
    |> List.of_enum
  in
  (constructors, uid_map)
;;

let create_continuation_type_spec
    (loc : Location.t) (type_name : string) (group : fragment_group)
  : continuation_type_spec =
  let constructors, uid_map =
    create_continuation_type_constructors group
  in
  let constructor_type_vars =
    constructors
    |> List.map
      (fun consdecl ->
         match consdecl.pcd_args with
         | Pcstr_tuple types ->
           types
           |> List.map tvars_of_type
           |> List.fold_left Tvar_set.union Tvar_set.empty
         | Pcstr_record _ ->
           raise @@ Utils.Invariant_failure(
             "Record variant constructor produced by " ^ "create_continuation_type_constructors"
           )
      )
    |> List.fold_left Tvar_set.union Tvar_set.empty
    |> Tvar_set.enum
    |> Enum.map
      (fun name ->
         { ptyp_desc = Ptyp_var name;
           ptyp_loc = loc;
           ptyp_attributes = [];
         }
      )
    |> Enum.map (fun t -> (t, Invariant))
    |> List.of_enum
  in
  let type_decl =
    { ptype_name = mkloc type_name loc;
      ptype_params = constructor_type_vars;
      ptype_cstrs = [];
      ptype_kind = Ptype_variant constructors;
      ptype_private = Public;
      ptype_manifest = None;
      ptype_attributes = [];
      ptype_loc = loc;
    }
  in
  { cts_bvs = create_big_variant type_decl;
    cts_uid_map = uid_map
  }
;;

let create_continuation_types
    (spec : continuation_type_spec)
  : type_declaration list =
  create_big_variant_types spec.cts_bvs
;;

let construct_continuation_value
    (loc : Location.t)
    (spec : continuation_type_spec)
    (uid : Fragment_uid.t)
    (args : expression list)
  : expression =
  let constructor_index = Fragment_uid_map.find uid spec.cts_uid_map in
  construct_big_variant loc spec.cts_bvs constructor_index args
;;

let destruct_continuation_value
    (loc : Location.t)
    (spec : continuation_type_spec)
    (uid : Fragment_uid.t)
    (pats : pattern list)
  : pattern =
  let constructor_index = Fragment_uid_map.find uid spec.cts_uid_map in
  destruct_big_variant loc spec.cts_bvs constructor_index pats
;;
