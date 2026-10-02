let rec name_with_generic_args_to_pattern_aux (ctx : ctx) (c : to_pat_config)
    (n : T.name) (generics : generic_args option) : pattern =
  match List.rev n, generics with
  | T.PeInstantiated binder :: reversed_prefix, (None | Some [])
    when binder.binder_params = TypesUtils.empty_generic_params ->
      let m = compute_constraints_map binder.binder_params in
      let instantiated_args =
        generic_args_to_pattern ctx c m binder.binder_value
      in
      name_with_generic_args_to_pattern_aux ctx c (List.rev reversed_prefix)
        (Some instantiated_args)
  | _ ->
  match n with
  | [] -> raise (Failure "Empty names are not valid")
  | [ e ] -> path_elem_with_generic_args_to_pattern ctx c e generics
  | e :: n ->
      path_elem_with_generic_args_to_pattern ctx c e None
      @ name_with_generic_args_to_pattern_aux ctx c n generics

and name_to_pattern_aux (ctx : ctx) (c : to_pat_config) (n : T.name) : pattern =
  name_with_generic_args_to_pattern_aux ctx c n None

and path_elem_with_generic_args_to_pattern (ctx : ctx) (c : to_pat_config)
    (e : T.path_elem) (generics : generic_args option) : pattern_elem list =
  match e with
  | PeIdent (s, d) -> begin
      let d = T.Disambiguator.to_int d in
      match generics with
      | None -> [ PIdent (s, d, []) ]
      | Some args -> [ PIdent (s, d, args) ]
    end
  | PeImpl impl -> [ impl_elem_to_pattern ctx c impl ]
  | PeTarget tgt -> begin
      match generics with
      | None -> [ PIdent (tgt, 0, []) ]
      | Some args -> [ PIdent (tgt, 0, args) ]
    end
  | PeInstantiated _ ->
      (* In pattern generation, we skip monomorphized elements since patterns
         are meant to match the logical structure, not the instantiation details *)
      []

and impl_elem_to_pattern (ctx : ctx) (c : to_pat_config) (impl : T.impl_elem) :
    pattern_elem =
  match impl with
  | ImplElemTy bound_ty ->
      PImpl (ty_to_pattern ctx c bound_ty.binder_params bound_ty.binder_value)
  | ImplElemTrait impl_id ->
      let impl = T.TraitImplId.Map.find impl_id ctx.crate.trait_impls in
      PImpl (trait_decl_ref_to_pattern ctx c impl.generics impl.impl_trait)

and trait_decl_ref_to_pattern (ctx : ctx) (c : to_pat_config)
    (params : T.generic_params) (tr : T.trait_decl_ref) : expr =
  (* Compute the constraints map *)
  let m = compute_constraints_map params in
  let generics = generic_args_to_pattern ctx c m tr.generics in
  (* Lookup the declaration *)
  let d = T.TraitDeclId.Map.find tr.id ctx.crate.trait_decls in
  EComp
    (name_with_generic_args_to_pattern_aux ctx c d.item_meta.name
       (Some generics))

and ty_to_pattern_aux (ctx : ctx) (c : to_pat_config) (m : constraints)
    (ty : T.ty) : expr =
  match ty with
  | TAdt tref -> (
      let generics = generic_args_to_pattern ctx c m tref.generics in
      match tref.id with
      | TAdtId id ->
          (* Lookup the declaration *)
          let d = T.TypeDeclId.Map.find id ctx.crate.type_decls in
          EComp
            (name_with_generic_args_to_pattern_aux ctx c d.item_meta.name
               (Some generics))
      | TTuple -> EPrimAdt (TTuple, generics)
      | TBuiltin TBox -> EComp [ PIdent ("Box", 0, generics) ]
      | TBuiltin TStr -> EComp [ PIdent ("str", 0, generics) ])
  | TVar v -> EVar (type_var_to_pattern m v)
  | TLiteral lit -> literal_type_to_pattern c lit
  | TRef (r, ty, rk) ->
      ERef
        ( region_to_pattern m r,
          ty_to_pattern_aux ctx c m ty,
          ref_kind_to_pattern rk )
  | TTraitType (trait_ref, type_id, generics) ->
      let type_name =
        GAstUtils.get_assoc_type_name ctx.crate
          trait_ref.trait_decl_ref.binder_value.id type_id
      in
      let name =
        trait_ref_item_with_generics_to_pattern ctx c m trait_ref type_name
          generics
      in
      EComp name
  | TFnPtr binder ->
      (* Push a regions map if necessary - TODO: make this more precise *)
      let m =
        constraints_map_push_regions_map_if_nonempty m binder.binder_regions
      in
      let { T.inputs; output; _ } = binder.binder_value in
      let inputs = List.map (ty_to_pattern_aux ctx c m) inputs in
      let output =
        if output = TypesUtils.mk_unit_ty then None
        else Some (ty_to_pattern_aux ctx c m output)
      in
      EArrow (inputs, output)
  | TRawPtr (ty, RMut) -> ERawPtr (Mut, ty_to_pattern_aux ctx c m ty)
  | TRawPtr (ty, RShared) -> ERawPtr (Not, ty_to_pattern_aux ctx c m ty)
  | TArray (ty, len) ->
      let generics =
        generic_args_to_pattern ctx c m
          {
            types = [ ty ];
            const_generics = [ len ];
            regions = [];
            trait_refs = [];
          }
      in
      EPrimAdt (TArray, generics)
  | TSlice ty ->
      let generics =
        generic_args_to_pattern ctx c m
          { types = [ ty ]; const_generics = []; regions = []; trait_refs = [] }
      in
      EPrimAdt (TSlice, generics)
  | _ -> EVar None

and trait_ref_item_with_generics_to_pattern (ctx : ctx) (c : to_pat_config)
    (m : constraints) (trait_ref : T.trait_ref) (item_name : string)
    (item_generics : T.generic_args) : pattern =
  if c.use_trait_decl_refs then
    let trait_decl_ref = trait_ref.trait_decl_ref in
    let d =
      T.TraitDeclId.Map.find trait_decl_ref.binder_value.id
        ctx.crate.trait_decls
    in
    (* Push a regions map if necessary - TODO: make this more precise *)
    let m =
      constraints_map_push_regions_map_if_nonempty m
        trait_decl_ref.binder_regions
    in
    let g =
      generic_args_to_pattern ctx c m trait_decl_ref.binder_value.generics
    in
    let name =
      name_with_generic_args_to_pattern_aux ctx c d.item_meta.name (Some g)
    in
    let item_generics = generic_args_to_pattern ctx c m item_generics in
    let name = name @ [ PIdent (item_name, 0, item_generics) ] in
    name
  else raise (Failure "TODO")

and ty_to_pattern (ctx : ctx) (c : to_pat_config) (params : T.generic_params)
    (ty : T.ty) : expr =
  (* Compute the constraints map *)
  let m = compute_constraints_map params in
  (* Convert the type *)
  ty_to_pattern_aux ctx c m ty

and constant_expr_to_pattern (ctx : ctx) (c : to_pat_config) (m : constraints)
    (cg : T.constant_expr) : generic_arg =
  match cg.kind with
  | CVar v -> GExpr (EVar (const_generic_var_to_pattern m v))
  | CLiteral v -> GValue (literal_to_pattern c v)
  | CGlobal gref ->
      let d = T.GlobalDeclId.Map.find gref.id ctx.crate.global_decls in
      let n = name_to_pattern_aux ctx c d.item_meta.name in
      GExpr (EComp n)
  | _ -> raise (Failure "TODO")

and generic_args_to_pattern (ctx : ctx) (c : to_pat_config) (m : constraints)
    (generics : T.generic_args) : generic_args =
  let ({ regions; types; const_generics; trait_refs = _ } : T.generic_args) =
    generics
  in
  let regions = List.map (region_to_pattern m) regions in
  let types = List.map (ty_to_pattern_aux ctx c m) types in
  let const_generics =
    List.map (constant_expr_to_pattern ctx c m) const_generics
  in
  List.concat
    [
      List.map (fun x -> GRegion x) regions;
      List.map (fun x -> GExpr x) types;
      const_generics;
    ]

