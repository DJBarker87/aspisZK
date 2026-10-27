import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Callee035
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `prover.prove_masked_with_attempt` (callee `aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1`).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  {T0 : Type} (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst :
  aspis_prover.state_only_hiding.StateOnlyMaskNonceStore T0) (public1 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (compiled :
  aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1) (variant : transport.Variant) (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (context : aspis_core.state_only_hiding.StateOnlyHidingContext) (binding : Array Std.U8 32#usize) (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (nonce_store : T0) :
  ∃ next, prover.prove_masked_with_attempt (T0 := T0) (aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst := aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst) (public1 := public1) (compiled := compiled) (variant := variant) (hash := hash) (context := context) (binding := binding) (attempt := attempt) (nonce_store := nonce_store) =
    (aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      aspis_proverstate_only_hidingStateOnlyMaskNonceStoreInst attempt hash
      binding context nonce_store >>= next) := by
  unfold prover.prove_masked_with_attempt
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Callee035
