import R1Z.ProverRwOuterGuardLeaves
import R1Z.ProverRwOuterAfterChecks
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterGuardBridge
open Aeneas Aeneas.Std Result ProverRwFull ProverRwOuterGuardLeaves
variable [ExternalTypes]

theorem checked (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize) (s : S) :
    letI : ExternalFuns := selected ops
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      store attempt hash binding (ProverRwOuterContextModel.context digest attempt.mask_nonce) s =
    ProverRwOuterAfterChecks.afterChecks store attempt hash binding
      (ProverRwOuterContextModel.context digest attempt.mask_nonce) s := by
  letI : ExternalFuns := selected ops
  unfold aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
    ProverRwOuterAfterChecks.afterChecks
  simp only [ProverRwOuterContextModel.context,array_ne_self,bind_tc_ok,
    Bool.false_eq_true,if_false,mask_installed,factor_installed]
  rfl

/-- The public framing theorem remains installed with both literal layout
leaves. Serializer, hash outcomes, reservation and entire proof body remain. -/
theorem caller (ops : ExternalFuns)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s : aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore) :
    letI : ExternalFuns := selected ops
    prover.prove_masked_attempt pub compiled v hash attempt s =
      ProverRwOuterCaller.caller pub compiled v hash attempt s :=
  ProverRwOuterCaller.source_entry {ops with op112 := mask,op113 := factor} pub compiled v hash attempt s

#print axioms checked
#print axioms caller
end R1Z.ProverRwOuterGuardBridge
