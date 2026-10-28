import R1Z.PV_RE_AfterChecksB10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_MaterialCellsC10
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)

/-- The source-selected layout leaves reach the actual material-cell callback.
The callback's entire continuation, including all inner errors, is retained. -/
theorem entered (ops : ExternalFuns) {S : Type}
    (inst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (hash : Hash) (binding digest nonce entropy : Array U8 32#usize) (store : S) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∃ next,
      aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
        inst hash binding (ProverRwOuterContextModel.context digest nonce) entropy store =
      (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1 >>= next) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  have hm : aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1 =
    .ok (ProverRwOuterContextModel.context digest nonce).mask_layout_fingerprint :=
    ProverRwOuterGuardLeaves.mask_installed {ops with op12 := @ProverRwOuterMapErr.map_err}
  have hf : aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1 =
    .ok (ProverRwOuterContextModel.context digest nonce).layout_factor_fingerprint :=
    ProverRwOuterGuardLeaves.factor_installed {ops with op12 := @ProverRwOuterMapErr.map_err}
  unfold aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
  simp only [hm,hf,bind_tc_ok,ProverRwOuterContextModel.context,
    Bool.false_eq_true,if_false]
  exact ⟨_,rfl⟩
#print axioms entered
end R1Z.PV_RE_MaterialCellsC10
