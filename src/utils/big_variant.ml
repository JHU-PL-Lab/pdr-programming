open Batteries;;

open Parsetree;;

open Utils;;

type big_variant_spec =
  { bvs_constructors : constructor_declaration Array.t;
    bvs_type_name : string;
    bvs_level_size : int;
    bvs_wrapper_constructor_name_fn : int -> string -> string;
  }
;;

let enum_array_region
    (start_idx : int) (end_idx : int) (array : 'a Array.t)
  : 'a Enum.t =
  let f idx =
    if idx >= end_idx then raise Enum.No_more_elements else (array.(idx), idx+1)
  in
  Enum.from_loop start_idx f
;;

let _default_wrapper_constructor_name_fn (level : int) (index : string)
  : string =
  Printf.sprintf "Wrapper%d_%s" level index
;;

let get_wrapper_constructor_name
    (constructor_index : int)
    (level : int)
    (bvs : big_variant_spec)
  : string =
  let constructor_count = Array.length bvs.bvs_constructors in
  let digits =
    1 + (int_of_float @@ floor @@ log10 @@
         float_of_int constructor_count)
  in
  let rec repeat n f x = if n = 0 then x else repeat (n-1) f (f x) in
  let effective_index =
    constructor_index
    |> repeat level (fun x -> x / bvs.bvs_level_size)
    |> repeat level (fun x -> x * bvs.bvs_level_size)
  in
  pad_string digits '0' @@ string_of_int effective_index
;;

let create_big_variant
    ?constructors_per_level:(level_size=200)
    ?wrapper_constructor_name_fn:
    (wrapper_constructor_name_fn=_default_wrapper_constructor_name_fn)
    (type_name : string)
    (constructor_declarations : constructor_declaration list)
  : big_variant_spec =
  { bvs_constructors = Array.of_list constructor_declarations;
    bvs_type_name = type_name;
    bvs_level_size = level_size;
    bvs_wrapper_constructor_name_fn = wrapper_constructor_name_fn;
  }
;;

let create_big_variant_types (loc : Location.t) (bvs : big_variant_spec)
  : type_declaration list =
  let constructor_count = Array.length bvs.bvs_constructors in
  let digits =
    1 + (int_of_float @@ floor @@ log10 @@ float_of_int constructor_count)
  in
  let level_count =
    int_of_float @@ floor @@
    log(float_of_int(constructor_count-1)) /.
    log(float_of_int bvs.bvs_level_size)
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
             float_of_int bvs.bvs_level_size then
            try_size
          else
            loop @@ try_size * bvs.bvs_level_size
        in
        loop bvs.bvs_level_size
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
             let padded_constructor_index_str =
               get_wrapper_constructor_name constructor_index level bvs
             in
             let wrapper_constructor_name =
               bvs.bvs_wrapper_constructor_name_fn
                 level
                 padded_constructor_index_str
             in
             { pcd_name = Location.mkloc wrapper_constructor_name loc;
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
        bvs.bvs_constructors
        |> enum_array_region start_idx end_idx
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
  create bvs.bvs_type_name level_count 0 constructor_count
  |> Deque.enum
  |> List.of_enum
;;

let construct_big_variant
    (loc : Location.t)
    (bvs : big_variant_spec)
    (constructor_index : int)
    (constructor_args : expression list)
  : expression =
  let constructor_count = Array.length bvs.bvs_constructors in
  let constructor = bvs.bvs_constructors.(constructor_index) in
  let constructor_args_expr_opt =
    if List.is_empty constructor_args then None else
    if List.length constructor_args = 1 then
      Some (List.first constructor_args)
    else
      Some
        { pexp_desc = Pexp_tuple(constructor_args);
          pexp_loc = loc;
          pexp_attributes = [];
        }
  in
  let level_count =
    int_of_float @@ floor @@
    log(float_of_int(constructor_count-1)) /.
    log(float_of_int bvs.bvs_level_size)
  in
  let rec loop level current_expr =
    if level > level_count then current_expr else
      let wrapper_name =
        get_wrapper_constructor_name constructor_index level bvs
      in
      loop (level + 1)
        { pexp_desc =
            Pexp_construct(
              Location.mkloc (Longident.Lident(wrapper_name)) loc,
              Some current_expr
            );
          pexp_loc = loc;
          pexp_attributes = [];
        }
  in
  loop 1 @@
  { pexp_desc =
      Pexp_construct(
        Location.mkloc (Longident.Lident constructor.pcd_name.txt) loc,
        constructor_args_expr_opt
      );
    pexp_loc = loc;
    pexp_attributes = [];
  }
;;

let destruct_big_variant
    (loc : Location.t)
    (bvs : big_variant_spec)
    (constructor_index : int)
    (argument_patterns : pattern list)
  : pattern =
  let constructor_count = Array.length bvs.bvs_constructors in
  let constructor = bvs.bvs_constructors.(constructor_index) in
  let destructor_pattern_opt =
    if List.is_empty argument_patterns then None else
    if List.length argument_patterns = 1 then
      Some (List.first argument_patterns)
    else
      Some
        { ppat_desc = Ppat_tuple(argument_patterns);
          ppat_loc = loc;
          ppat_attributes = [];
        }
  in
  let level_count =
    int_of_float @@ floor @@
    log(float_of_int(constructor_count-1)) /.
    log(float_of_int bvs.bvs_level_size)
  in
  let rec loop level current_expr =
    if level > level_count then current_expr else
      let wrapper_name =
        get_wrapper_constructor_name constructor_index level bvs
      in
      loop (level + 1)
        { ppat_desc =
            Ppat_construct(
              Location.mkloc (Longident.Lident(wrapper_name)) loc,
              Some current_expr
            );
          ppat_loc = loc;
          ppat_attributes = [];
        }
  in
  loop 1 @@
  { ppat_desc =
      Ppat_construct(
        Location.mkloc (Longident.Lident constructor.pcd_name.txt) loc,
        destructor_pattern_opt
      );
    ppat_loc = loc;
    ppat_attributes = [];
  }
;;
