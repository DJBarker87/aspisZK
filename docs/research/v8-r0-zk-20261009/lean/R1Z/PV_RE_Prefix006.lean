import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix006
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref` (op112).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {T0 : Type} (StateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (precommit_binding : Array Std.U8 32#usize) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (private_entropy : Array Std.U8 32#usize) (nonce_store : T0) :
  ∃ next, @aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref _ _ T0 StateOnlyMaskNonceStoreInst hash precommit_binding context private_entropy nonce_store =
    (aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1 >>= next) := by
  unfold aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix006
