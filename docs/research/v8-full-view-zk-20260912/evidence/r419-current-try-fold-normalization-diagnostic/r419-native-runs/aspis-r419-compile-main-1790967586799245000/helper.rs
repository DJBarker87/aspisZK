//! Pure native-AST helpers for eliminating one type parameter by an
//! associated-type projection. This file is a draft snippet, not wired into
//! PrePasses and not compiled.

use charon_lib::ast::*;
use charon_lib::ids::IndexVec;
use index_vec::Idx;

/// The AST representation of the generic being transformed.
///
/// `Free` is used by function signatures when Charon's free-variable option
/// is enabled. `Bound` means precisely a variable bound at depth zero from
/// the visitor's current outside view. Other bound depths are never matched.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scope {
    Free,
    Bound,
}

fn scoped_id(v: TypeDbVar, scope: Scope) -> Option<TypeVarId> {
    match (scope, v) {
        (Scope::Free, DeBruijnVar::Free(id)) => Some(id),
        (Scope::Bound, DeBruijnVar::Bound(db, id)) if db == DeBruijnId::ZERO => Some(id),
        _ => None,
    }
}

fn in_scope(id: TypeVarId, scope: Scope) -> TypeDbVar {
    match scope {
        Scope::Free => DeBruijnVar::Free(id),
        Scope::Bound => DeBruijnVar::Bound(DeBruijnId::ZERO, id),
    }
}

/// Detect a reference to `slot` in the matching variable mode.
///
/// Charon's visitor reports variables as seen from outside the value, so an
/// outer Bound-0 reference remains detectable under nested binders while a
/// variable local to a nested binder is not mistaken for it.
pub fn has_slot<T: TyVisitable + Clone>(value: &T, slot: TypeVarId, scope: Scope) -> bool {
    struct Probe {
        slot: TypeVarId,
        scope: Scope,
        found: bool,
    }
    impl VarsVisitor for Probe {
        fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
            if scoped_id(v, self.scope) == Some(self.slot) {
                self.found = true;
            }
            None
        }
    }

    let mut copy = value.clone();
    let mut probe = Probe { slot, scope, found: false };
    copy.visit_vars(&mut probe);
    probe.found
}

struct ReindexVisitor {
    slot: TypeVarId,
    scope: Scope,
}
impl VarsVisitor for ReindexVisitor {
    fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
        let id = scoped_id(v, self.scope)?;
        if id.index() > self.slot.index() {
            Some(TyKind::TypeVar(in_scope(TypeVarId::from(id.index() - 1), self.scope)).into_ty())
        } else {
            None
        }
    }
}

/// Return the input projection with matching-mode indices above `slot`
/// reindexed for the declaration with that slot removed. A same-mode
/// reference to `slot` is rejected, since this replacement must be independent
/// of the parameter it replaces.
pub fn replacement(projection: Ty, slot: TypeVarId, scope: Scope) -> Ty {
    assert!(
        !has_slot(&projection, slot, scope),
        "projection refers to the type parameter being removed"
    );
    let mut out = projection;
    out.visit_vars(&mut ReindexVisitor { slot, scope });
    out
}

struct RewriteVisitor<'a> {
    slot: TypeVarId,
    scope: Scope,
    projection: &'a Ty,
}
impl VarsVisitor for RewriteVisitor<'_> {
    fn visit_type_var(&mut self, v: TypeDbVar) -> Option<Ty> {
        let id = scoped_id(v, self.scope)?;
        if id == self.slot {
            Some(self.projection.clone())
        } else if id.index() > self.slot.index() {
            Some(TyKind::TypeVar(in_scope(TypeVarId::from(id.index() - 1), self.scope)).into_ty())
        } else {
            None
        }
    }
}

/// Replace matching-mode `slot` references with an already reindexed
/// projection, and decrement the remaining matching-mode indices above it.
/// Other Free/Bound variables, binder depths, regions, constants, and clauses
/// are left to Charon's native `visit_vars` traversal unchanged.
pub fn rewrite<T: TyVisitable>(
    value: &mut T,
    slot: TypeVarId,
    scope: Scope,
    reindexed_projection: &Ty,
) {
    value.visit_vars(&mut RewriteVisitor { slot, scope, projection: reindexed_projection });
}

/// Remove only the explicit type-parameter declaration at `slot`. The
/// `IndexVec` positions of retained type declarations become their new ids.
/// This deliberately leaves every region, const generic, trait clause,
/// outlives predicate, and associated-type constraint untouched.
pub fn remove_param(params: &mut GenericParams, slot: TypeVarId) {
    assert!(slot.index() < params.types.len(), "type parameter slot is out of range");
    let old = std::mem::replace(&mut params.types, IndexVec::new());
    for (index, param) in old.iter().enumerate() {
        if index != slot.index() {
            let new_id = TypeVarId::from(params.types.len());
            let mut retained = param.clone();
            retained.index = new_id;
            let pushed_id = params.types.push(retained);
            debug_assert_eq!(pushed_id, new_id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn projection(var: TypeDbVar) -> Ty {
        let self_ty = TyKind::TypeVar(var).into_ty();
        let trait_decl_ref = RegionBinder::empty(TraitDeclRef {
            id: TraitDeclId::from(0usize),
            generics: Box::new(GenericArgs::new_types([self_ty].into())),
        });
        let tref = TraitRef::new(TraitRefKind::SelfId, trait_decl_ref);
        TyKind::TraitType(tref, AssocTypeId::from(0usize), GenericArgs::empty()).into_ty()
    }

    #[test]
    fn projection_scope_is_preserved_under_region_binder() {
        let slot = TypeVarId::from(1usize);
        let free_projection = projection(DeBruijnVar::Free(slot));
        assert!(has_slot(&free_projection, slot, Scope::Free));
        assert!(!has_slot(&free_projection, slot, Scope::Bound));

        // RegionBinder::empty moves an outer Bound-0 reference under the
        // projection's nested region binder. `visit_vars` reports it back as
        // Bound-0, while Free references remain a separate namespace.
        let bound_projection = projection(DeBruijnVar::Bound(DeBruijnId::ZERO, slot));
        assert!(has_slot(&bound_projection, slot, Scope::Bound));
        assert!(!has_slot(&bound_projection, slot, Scope::Free));
    }

    #[test]
    fn replacement_reindexes_only_the_selected_mode() {
        let slot = TypeVarId::from(1usize);
        let old_later = TypeVarId::from(3usize);
        let shifted = replacement(projection(DeBruijnVar::Free(old_later)), slot, Scope::Free);
        assert!(has_slot(&shifted, TypeVarId::from(2usize), Scope::Free));
        assert!(!has_slot(&shifted, old_later, Scope::Free));
        assert!(!has_slot(&shifted, TypeVarId::from(2usize), Scope::Bound));
    }

    #[test]
    fn rewrite_substitutes_projection_and_does_not_cross_modes() {
        let slot = TypeVarId::from(1usize);
        let old_later = TypeVarId::from(3usize);
        let mut value = projection(DeBruijnVar::Free(slot));
        let projected = replacement(projection(DeBruijnVar::Free(old_later)), slot, Scope::Free);
        rewrite(&mut value, slot, Scope::Free, &projected);
        assert!(!has_slot(&value, slot, Scope::Free));
        assert!(has_slot(&value, TypeVarId::from(2usize), Scope::Free));
    }

    #[test]
    fn bound_rewrite_crosses_nested_region_binder_without_changing_mode() {
        let slot = TypeVarId::from(1usize);
        let old_later = TypeVarId::from(3usize);
        let mut value = projection(DeBruijnVar::Bound(DeBruijnId::ZERO, slot));
        let projected = replacement(
            projection(DeBruijnVar::Bound(DeBruijnId::ZERO, old_later)),
            slot,
            Scope::Bound,
        );
        rewrite(&mut value, slot, Scope::Bound, &projected);
        assert!(!has_slot(&value, slot, Scope::Bound));
        assert!(has_slot(&value, TypeVarId::from(2usize), Scope::Bound));
        assert!(!has_slot(&value, TypeVarId::from(2usize), Scope::Free));
    }

    #[test]
    fn adjacent_later_variable_becomes_new_slot_without_recursive_rewrite() {
        let old_slot = TypeVarId::from(1usize);
        let original_later = TypeVarId::from(2usize);
        let reindexed = replacement(
            TyKind::TypeVar(DeBruijnVar::Free(original_later)).into_ty(),
            old_slot,
            Scope::Free,
        );
        // It is now new slot 1. `rewrite` inserts this node at its exit-time
        // visitor callback and must not traverse the inserted node again.
        assert!(has_slot(&reindexed, old_slot, Scope::Free));
        let mut value = TyKind::TypeVar(DeBruijnVar::Free(old_slot)).into_ty();
        rewrite(&mut value, old_slot, Scope::Free, &reindexed);
        assert_eq!(value, reindexed);
    }

    #[test]
    fn type_binder_protects_local_variable_and_shifts_replacement() {
        let outer_slot = TypeVarId::from(1usize);
        let earlier_outer = TypeVarId::from(0usize);
        let local_id = TypeVarId::from(0usize);
        let mut nested_params = GenericParams::empty();
        nested_params.types.push(TypeParam::new(local_id, "Inner".to_owned()));

        let local = TyKind::TypeVar(DeBruijnVar::Bound(DeBruijnId::ZERO, local_id)).into_ty();
        let outer = TyKind::TypeVar(DeBruijnVar::Bound(DeBruijnId::one(), outer_slot)).into_ty();
        let mut value = Binder::new(
            BinderKind::Other,
            nested_params,
            Ty::mk_tuple(vec![local.clone(), outer]),
        );
        let projection =
            TyKind::TypeVar(DeBruijnVar::Bound(DeBruijnId::ZERO, earlier_outer)).into_ty();
        rewrite(&mut value, outer_slot, Scope::Bound, &projection);

        let fields = value.skip_binder.as_tuple().unwrap();
        assert_eq!(fields[TypeVarId::from(0usize)], local);
        assert_eq!(
            fields[TypeVarId::from(1usize)],
            TyKind::TypeVar(DeBruijnVar::Bound(DeBruijnId::one(), earlier_outer)).into_ty(),
        );
        assert!(!has_slot(&value, outer_slot, Scope::Bound));
    }

    #[test]
    #[should_panic(expected = "projection refers to the type parameter being removed")]
    fn replacement_rejects_self_occurrence() {
        let slot = TypeVarId::from(1usize);
        let _ = replacement(projection(DeBruijnVar::Free(slot)), slot, Scope::Free);
    }
}
