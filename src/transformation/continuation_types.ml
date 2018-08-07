(**
   This module defines routines relating to the continuation types generated for
   PDR programs.  A continuation type is a variant which contains the
   information necessary to represent a continuation.
*)

open Batteries;;
(* open Jhupllib;; *)

open Parsetree;;

open Pdr_programming_continuation_extensions.Fragment_types;;
open Pdr_programming_utils.Variable_utils;;

exception Invalid_constructor_argument_list of string;;
exception Untyped_continuation_variable of Longident.t * Location.t;;

(* If there are more than 246 non-constant constructors in an OCaml variant
   type, the OCaml compiler rejects the declaration.  This is due to OCaml's
   runtime memory layout for variant types.  To get around this, we can just
   create a series of dedicated wrapper types.  That is, we'll have:

     type foo = Wrapper1_000 of foo_0 | Wrapper1_200 of foo_1 | ...
     type foo_0 = C000 of ... | C001 of ... | ...
     type foo_1 = C200 of ... | C201 of ... | ...

   If necessary, we can even wrap further (foo_0_0, etc.).

   Given the index of a constructor and the largest index of any constructor, we
   can compute the position in the tree of wrappers that the constructor would
   take.  For instance, constructor number 12,500 in a set of 50,000
   constructors would be called something like
       Wrapper2_00000(Wrapper1_12400(C12500(...)))
   Here, the outermost type (say, "foo") would have two constructors:
   Wrapper2_00000 (ranging over the first 40,000 constructors) and
   Wrapper2_40000 (randing over the last 10,000 constructors).  The single
   argument to Wrapper2_00000 would be an element of a type (say, "foo_0")
   which itself would contain 200 constructors: Wrapper1_00000, Wrapper1_00200,
   Wrapper1_00400, and so on.  Each of these constructors would take a single
   argument of a similar type (say, "foo_0_0" for Wrapper1_00000, "foo_0_1" for
   Wrapper1_00200, and so on).  These types would contain the actual
   constructors for the continuations.
*)

let maximum_constructors_per_level = 200;;

type continuation_construction_context =
  { ccc_entries : int;
    ccc_id_map : int Fragment_uid_map.t;
  }
;;

type continuation_constructor =
  { cc_index : int;
    cc_name : string;
    cc_types : core_type list;
    cc_loc : Location.t;
  }
;;

type continuation_type_spec =
  { cts_entries : int;
    cts_constructors : continuation_constructor Array.t;
    cts_id_map : int Fragment_uid_map.t;
  }
;;

let pad_string n c s =
  if String.length s < n then
    String.make (n - String.length s) c ^ s
  else
    s
;;

let enum_array_region
    (start_idx : int) (end_idx : int) (array : 'a Array.t)
  : 'a Enum.t =
  let f idx =
    if idx >= end_idx then raise Enum.No_more_elements else (array.(idx), idx+1)
  in
  Enum.from_loop start_idx f
;;

let constructor_name (constructor_index : int) (entries : int) : string =
  let digits =
    1 + (int_of_float @@ floor @@ log10 @@ float_of_int entries)
  in
  let id_str = string_of_int constructor_index in
  let id_constr_str = pad_string digits '0' id_str in
  "Continuation_" ^ id_constr_str
;;

let wrapper_name (level : int) (constructor_index : int) (entries : int)
  : string =
  let digits =
    1 + (int_of_float @@ floor @@ log10 @@ float_of_int entries)
  in
  let rec repeat n f x = if n = 0 then x else repeat (n-1) f (f x) in
  let effective_index =
    constructor_index
    |> repeat level (fun x -> x / maximum_constructors_per_level)
    |> repeat level (fun x -> x * maximum_constructors_per_level)
  in
  Printf.sprintf "Wrapper%d_%s"
    level (pad_string digits '0' @@ string_of_int effective_index)
;;

let create_continuation_constructor
    (context : continuation_construction_context)
    (fragment : fragment)
  : continuation_constructor =
  let id_map = context.ccc_id_map in
  let id_int = Fragment_uid_map.find fragment.fragment_uid id_map in
  let constr_name = constructor_name id_int context.ccc_entries in
  let constr_types =
    fragment.fragment_externally_bound_variables
    |> Var_map.enum
    |> Enum.map
      (fun (_,ebv) ->
         match ebv.ebv_type with
         | Some t -> t
         | None ->
           raise @@ Untyped_continuation_variable(
             ebv.ebv_variable, ebv.ebv_bind_loc)
      )
    |> List.of_enum
  in
  { cc_index = id_int;
    cc_name = constr_name;
    cc_types = constr_types;
    cc_loc = fragment.fragment_loc;
  }
;;

let create_continuation_type_spec
    (group : fragment_group)
  : continuation_type_spec =
  let fragment_count = Fragment_uid_map.cardinal group.fg_graph in
  let indices = (0 --^ fragment_count) in
  let id_map =
    group.fg_graph
    |> Fragment_uid_map.enum
    |> (fun x -> Enum.combine (indices,x))
    |> Enum.map (fun (idx, (uid, _)) -> (uid, idx))
    |> Fragment_uid_map.of_enum
  in
  let context =
    { ccc_entries = fragment_count;
      ccc_id_map = id_map;
    }
  in
  let constructors =
    group.fg_graph
    |> Fragment_uid_map.enum
    |> Enum.map
      (fun (_,fragment) -> create_continuation_constructor context fragment)
    |> Array.of_enum
  in
  { cts_entries = fragment_count;
    cts_id_map = id_map;
    cts_constructors = constructors;
  }
;;

let create_continuation_constructor_declaration
    (constr : continuation_constructor)
  : constructor_declaration =
  { pcd_name = Location.mkloc constr.cc_name constr.cc_loc;
    pcd_args = Pcstr_tuple constr.cc_types;
    pcd_res = None;
    pcd_loc = constr.cc_loc;
    pcd_attributes = [];
  }
;;

let create_continuation_type_declarations
    (loc : Location.t)
    (type_name : string)
    (spec : continuation_type_spec)
  : type_declaration list =
  let digits =
    1 + (int_of_float @@ floor @@ log10 @@ float_of_int spec.cts_entries)
  in
  let level_count =
    int_of_float @@ floor @@
    log(float_of_int(spec.cts_entries-1)) /.
    log(float_of_int maximum_constructors_per_level)
  in
  let rec create
      (type_name : string)
      (level : int)
      (start_idx : int)
      (end_idx : int)
    : type_declaration Deque.t =
    let num_constructors = end_idx - start_idx in
    if level > 0 then
      (* We'll split the type into a bunch of chunks.  We'll then create a
         wrapper for each chunk. *)
      let level_size =
        let rec loop try_size =
          if float_of_int num_constructors /. float_of_int try_size <=
             float_of_int maximum_constructors_per_level then
            try_size
          else
            loop @@ try_size * maximum_constructors_per_level
        in
        loop maximum_constructors_per_level
      in
      let rec make_inner (constr_idx : int) (type_idx : int)
        : (string * int) list * type_declaration Deque.t =
        if constr_idx >= end_idx then ([], Deque.empty) else
          let inner_type_name =
            (type_name ^ "_" ^ pad_string digits '0' (string_of_int constr_idx))
          in
          let decls =
            create
              inner_type_name
              (level - 1)
              constr_idx
              (min end_idx (constr_idx + level_size))
          in
          let (wrapper_data, rec_decls) =
            make_inner (constr_idx + level_size) (type_idx + 1)
          in
          ( (inner_type_name, constr_idx) :: wrapper_data,
            Deque.append decls rec_decls
          )
      in
      let (wrapper_data, decls) = make_inner start_idx 0 in
      let wrapper_constructors : constructor_declaration list =
        wrapper_data
        |> List.map
          (fun (inner_type_name, constructor_index) ->
             let name = wrapper_name level constructor_index spec.cts_entries in
             { pcd_name = Location.mkloc name loc;
               pcd_args = Pcstr_tuple([
                   { ptyp_desc = Ptyp_constr(
                         Location.mkloc (Longident.Lident inner_type_name) loc,
                         []
                       );
                     ptyp_loc = loc;
                     ptyp_attributes = [];
                   }
                 ]);
               pcd_res = None;
               pcd_loc = loc;
               pcd_attributes = [];
             }
          )
      in
      let wrapper_decl =
        { ptype_name = Location.mkloc type_name loc;
          ptype_params = []; (* See TODO below. *)
          ptype_cstrs = [];
          ptype_kind = Ptype_variant(wrapper_constructors);
          ptype_private = Public;
          ptype_manifest = None;
          ptype_attributes = [];
          ptype_loc = loc;
        }
      in
      Deque.snoc decls wrapper_decl
    else
      let constructor_declarations =
        spec.cts_constructors
        |> enum_array_region start_idx end_idx
        |> Enum.map create_continuation_constructor_declaration
        |> List.of_enum
      in
      Deque.cons
        { ptype_name = Location.mkloc type_name loc;
          ptype_params = [];
          (* TODO: What about one parameter for each argument position?  Could
             we eliminate the need for type signatures just by making every
             position in the type polymorphic?  Functions which use these types
             will have to declare them as having an enormous number of type variables, but OCaml type variables aren't necessarily universally
             quantified; we could actually make use of that here!  (The OCaml
             compiler doesn't seem to mind a variant type declaration with
             over 80,000 polymorphic type variables.) *)
          ptype_cstrs = [];
          ptype_kind = Ptype_variant(constructor_declarations);
          ptype_private = Public;
          ptype_manifest = None;
          ptype_attributes = [];
          ptype_loc = loc;
        }
        Deque.empty
  in
  create type_name level_count 0 spec.cts_entries
  |> Deque.enum
  |> List.of_enum
;;

let call_constructor
    (loc : Location.t)
    (spec : continuation_type_spec)
    (uid : Fragment_uid.t)
    (args : expression list)
  : expression =
  let index = Fragment_uid_map.find uid spec.cts_id_map in
  let constructor = spec.cts_constructors.(index) in
  let types = constructor.cc_types in
  if List.length args != List.length types then
    raise @@ Invalid_constructor_argument_list(
      Printf.sprintf
        "Length of argument list (%d) must match length of constructor types (%d)"
        (List.length args) (List.length constructor.cc_types)
    );
  let args_expr_opt =
    if List.is_empty args then None else
    if List.length args = 1 then Some (List.first args) else
      Some
        { pexp_desc = Pexp_tuple(args);
          pexp_loc = loc;
          pexp_attributes = [];
        }
  in
  let level_count =
    int_of_float @@ floor @@
    log(float_of_int(spec.cts_entries-1)) /.
    log(float_of_int maximum_constructors_per_level)
  in
  let rec loop level current_expr =
    if level = 0 then current_expr else
      loop (level - 1)
        { pexp_desc =
            Pexp_construct(
              Location.mkloc (Longident.Lident(
                  wrapper_name level index spec.cts_entries
                )) loc,
              Some current_expr
            );
          pexp_loc = loc;
          pexp_attributes = [];
        }
  in
  loop level_count @@
  { pexp_desc =
      Pexp_construct(
        Location.mkloc (Longident.Lident constructor.cc_name) loc, args_expr_opt
      );
    pexp_loc = loc;
    pexp_attributes = [];
  }
;;
