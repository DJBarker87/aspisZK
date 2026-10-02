use charon_lib::ast::*;
use charon_lib::ids::IndexVec;
use super::helper::{Scope,replacement,rewrite,remove_param};

// Additional uncompiled R419 fixture draft.
//
// Intended to be placed inside the existing helper `#[cfg(test)]` module.
// These fixtures exercise only AST rewrite/substitution mechanics; they do
// not execute Charon's LLBC transform or establish source correspondence.

#[test]
fn removing_middle_type_slot_preserves_names_indices_and_other_vectors() {
    let mut params = GenericParams::empty();
    for index in 0..4 {
        params.types.push(TypeParam::new(
            TypeVarId::from(index),
            format!("T{index}"),
        ));
    }
    // Keep a non-type generic vector nonempty as well. The remaining vectors
    // are snapshotted explicitly so any accidental mutation is detected.
    params
        .regions
        .push(RegionParam::new(RegionId::from(0usize), None));
    let regions_before = params.regions.clone();
    let consts_before = params.const_generics.clone();
    let clauses_before = params.trait_clauses.clone();
    let regions_outlive_before = params.regions_outlive.clone();
    let types_outlive_before = params.types_outlive.clone();
    let constraints_before = params.trait_type_constraints.clone();

    remove_param(&mut params, TypeVarId::from(1usize));

    assert_eq!(params.types.len(), 3);
    for (new_index, old_index) in [0usize, 2, 3].into_iter().enumerate() {
        let id = TypeVarId::from(new_index);
        assert_eq!(params.types[id].index, id);
        assert_eq!(params.types[id].name.as_str(), format!("T{old_index}"));
    }
    assert_eq!(params.regions, regions_before);
    assert_eq!(params.const_generics, consts_before);
    assert_eq!(params.trait_clauses, clauses_before);
    assert_eq!(params.regions_outlive, regions_outlive_before);
    assert_eq!(params.types_outlive, types_outlive_before);
    assert_eq!(params.trait_type_constraints, constraints_before);
}

#[test]
#[should_panic(expected = "projection refers to the type parameter being removed")]
fn replacement_rejects_removed_free_slot() {
    let slot = TypeVarId::from(1usize);
    let _ = replacement(
        TyKind::TypeVar(DeBruijnVar::Free(slot)).into_ty(),
        slot,
        Scope::Free,
    );
}

#[test]
#[should_panic(expected = "projection refers to the type parameter being removed")]
fn replacement_rejects_removed_bound_slot() {
    let slot = TypeVarId::from(1usize);
    let _ = replacement(
        TyKind::TypeVar(DeBruijnVar::Bound(DeBruijnId::ZERO, slot)).into_ty(),
        slot,
        Scope::Bound,
    );
}

#[test]
fn constraint_region_bound_by_its_region_binder_cannot_escape() {
    let region_id = RegionId::from(0usize);
    let mut regions = IndexVec::new();
    regions.push(RegionParam::new(region_id, None));
    let escaping = TyKind::Ref(
        Region::Var(DeBruijnVar::Bound(DeBruijnId::ZERO, region_id)),
        Ty::mk_tuple(vec![]),
        RefKind::Shared,
    )
    .into_ty();
    let trait_ref = TraitRef::new(
        TraitRefKind::SelfId,
        RegionBinder::empty(TraitDeclRef {
            id: TraitDeclId::from(0usize),
            generics: Box::new(GenericArgs::empty()),
        }),
    );
    let constraint = RegionBinder {
        regions,
        skip_binder: TraitTypeConstraint {
            trait_ref,
            type_id: AssocTypeId::from(0usize),
            ty: escaping.clone(),
        },
    };

    assert!(constraint.skip_binder.ty.clone().move_from_under_binder().is_none());
    assert_eq!(constraint.skip_binder.ty, escaping);
}

fn associated_trait_ref(self_ty: Ty) -> TraitRef {
    let trait_decl_ref = RegionBinder::empty(TraitDeclRef {
        id: TraitDeclId::from(0usize),
        generics: Box::new(GenericArgs::new_types([self_ty].into())),
    });
    TraitRef::new(TraitRefKind::SelfId, trait_decl_ref)
}

fn associated_output(self_ty: Ty) -> Ty {
    let trait_ref = associated_trait_ref(self_ty);
    TyKind::TraitType(trait_ref, AssocTypeId::from(0usize), GenericArgs::empty()).into_ty()
}

#[test]
fn forgetting_old_b_argument_reconstructs_the_same_instantiated_signature() {
    let old_a = TypeVarId::from(0usize);
    let old_b = TypeVarId::from(1usize);
    let mut old_decl_params = GenericParams::empty();
    old_decl_params
        .types
        .push(TypeParam::new(old_a, "A".to_owned()));
    old_decl_params
        .types
        .push(TypeParam::new(old_b, "B".to_owned()));
    let projection = associated_output(TyKind::TypeVar(DeBruijnVar::Free(old_a)).into_ty());
    let new_projection = replacement(projection, old_b, Scope::Free);
    let old_b_type = TyKind::TypeVar(DeBruijnVar::Free(old_b)).into_ty();
    let old_a_type = TyKind::TypeVar(DeBruijnVar::Free(old_a)).into_ty();
    old_decl_params.trait_type_constraints.push(RegionBinder::empty(
        TraitTypeConstraint {
            trait_ref: associated_trait_ref(old_a_type.clone()),
            type_id: AssocTypeId::from(0usize),
            ty: old_b_type.clone(),
        },
    ));
    let mut new_decl_params = old_decl_params.clone();
    rewrite(&mut new_decl_params.trait_type_constraints, old_b, Scope::Free, &new_projection);
    let equality = &new_decl_params.trait_type_constraints[
        TraitTypeConstraintId::from(0usize)
    ]
    .skip_binder;
    let reflexive_projection = TyKind::TraitType(
        equality.trait_ref.clone(),
        equality.type_id,
        GenericArgs::empty(),
    )
    .into_ty();
    assert_eq!(equality.ty, reflexive_projection);
    new_decl_params.trait_type_constraints.clear();
    remove_param(&mut new_decl_params, old_b);
    assert!(new_decl_params.trait_type_constraints.is_empty());
    assert_eq!(new_decl_params.types.len(), 1);
    assert_eq!(new_decl_params.types[TypeVarId::from(0usize)].name.as_str(), "A");

    // Model an old declaration with `<A, B>` and a rewritten declaration
    // with `<A>`. The first input/output use B; after rewriting they use the
    // associated projection over A. The second input is A in both.
    let old_signature_types = Ty::mk_tuple(vec![
        old_b_type.clone(),
        old_a_type.clone(),
        old_b_type.clone(),
    ]);
    let mut rewritten_signature = old_signature_types.clone();
    rewrite(
        &mut rewritten_signature,
        old_b,
        Scope::Free,
        &new_projection,
    );

    // Concrete call-site arguments instantiate old B with the associated
    // output of concrete A. Removing B from the call-site argument vector
    // leaves just concrete A for the rewritten declaration.
    let concrete_a = Ty::mk_tuple(vec![]);
    let concrete_b = associated_output(concrete_a.clone());
    let old_call_args = GenericArgs::new_types([concrete_a.clone(), concrete_b].into());
    let old_callsite = FunDeclRef {
        id: FunDeclId::from(0usize),
        generics: Box::new(old_call_args),
    };
    let mut new_callsite = old_callsite.clone();
    new_callsite.generics.types = std::mem::take(&mut new_callsite.generics.types)
        .into_iter()
        .enumerate()
        .filter_map(|(index, ty)| (index != old_b.index()).then_some(ty))
        .collect();
    let new_call_args = &new_callsite.generics;
    assert_eq!(new_call_args.types.len(), 1);

    let old_instantiated_b = instantiate_free(old_b_type, &old_callsite.generics);
    let new_instantiated_output = instantiate_free(new_projection, new_call_args);
    assert_eq!(old_instantiated_b, new_instantiated_output);

    let old_instantiated_signature = instantiate_free(old_signature_types, &old_callsite.generics);
    let new_instantiated_signature = instantiate_free(rewritten_signature, new_call_args);
    assert_eq!(old_instantiated_signature, new_instantiated_signature);
}

fn instantiate_free(mut value:Ty,args:&GenericArgs)->Ty {
    struct Bind;
    impl VarsVisitor for Bind {
        fn visit_type_var(&mut self,v:TypeDbVar)->Option<Ty> {
            match v {
                DeBruijnVar::Free(id)=>Some(TyKind::TypeVar(DeBruijnVar::Bound(DeBruijnId::ZERO,id)).into_ty()),
                _=>None,
            }
        }
    }
    value.visit_vars(&mut Bind);
    value.try_substitute_with_self(args,&TraitRefKind::SelfId).unwrap()
}
