(* UNVERIFIED R424 focused concrete associated-type reducer.
   No region erasure and no modification of RegionsHierarchy's invariant.
   Initially accepts only empty associated-item binders whose source value
   contains no nested binders. Other cases fail explicitly. *)
open Types
open LlbcAst

let reject span message = [%craise_opt_span] span message

let empty_params (p : generic_params) =
  p.regions = [] && p.types = [] && p.const_generics = []
  && p.trait_clauses = [] && p.regions_outlive = []
  && p.types_outlive = [] && p.trait_type_constraints = []

let empty_args (a : generic_args) =
  a.regions = [] && a.types = [] && a.const_generics = []
  && a.trait_refs = []

let require_no_source_binders span (ty : ty) =
  let visitor = object
    inherit [_] iter_ty
    method! visit_binder _ _ _ =
      reject span "R424: nested associated-value binder is unsupported"
    method! visit_region_binder _ _ _ =
      reject span "R424: nested associated-value region binder is unsupported"
  end in
  visitor#visit_ty () ty

let normalize_visitor span (crate : crate) =
  object (self)
    inherit [_] map_ty as super

    method! visit_ty stack ty =
      let ty = super#visit_ty stack ty in
      match ty with
      | TTraitType (tref, type_id, assoc_args) ->
          (match tref.kind with
          | TraitImpl impl_ref ->
              if List.length stack >= 128 || List.mem ty stack then
                reject span "R424: recursive concrete associated-type reduction";
              let timpl = match TraitImplId.Map.find_opt impl_ref.id crate.trait_impls with
                | Some timpl -> timpl
                | None -> reject span "R424: missing concrete trait implementation" in
              if tref.trait_decl_ref.binder_regions <> [] then
                reject span "R424: higher-ranked concrete implementation reference is unsupported";
              let impl_subst =
                Substitute.make_subst_from_generics __FILE__ __LINE__ span
                  timpl.generics impl_ref.generics tref.kind in
              let expected_trait =
                Substitute.trait_decl_ref_substitute impl_subst timpl.impl_trait in
              (* Remove the empty region binder with the native rejecting
                 substitution: any escaping local bound variable is an error. *)
              let actual_trait =
                Substitute.trait_decl_ref_substitute
                  (Substitute.subst_remove_binder_zero Substitute.error_sb_subst)
                  tref.trait_decl_ref.binder_value in
              if expected_trait <> actual_trait then
                reject span "R424: concrete implementation trait instantiation mismatch";
              let assoc = match AssocTypeId.Map.find_opt type_id timpl.types with
                | Some assoc -> assoc
                | None -> reject span "R424: missing concrete associated-type definition" in
              if not (empty_params assoc.binder_params && empty_args assoc_args) then
                reject span "R424: generic associated-type binder is unsupported";
              if assoc.binder_value.implied_trait_refs <> [] then
                reject span "R424: unlifted associated-type predicates are unsupported";
              require_no_source_binders span assoc.binder_value.value;
              (* Remove the associated binder first. This avoids moving an
                 arbitrary replacement argument under an unnecessary binder.
                 A source value with nested binders was rejected above. *)
              let assoc = Substitute.apply_args_to_binder assoc_args
                Substitute.st_substitute_visitor#visit_trait_assoc_ty_impl assoc in
              let replacement =
                Substitute.apply_args_to_item_binder tref.kind impl_ref.generics
                  Substitute.st_substitute_visitor#visit_ty
                  { item_binder_params = timpl.generics;
                    item_binder_value = assoc.value } in
              self#visit_ty (ty :: stack) replacement
          | _ -> ty)
      | _ -> ty
  end

let normalize_ty span crate ty =
  (normalize_visitor span crate)#visit_ty [] ty
