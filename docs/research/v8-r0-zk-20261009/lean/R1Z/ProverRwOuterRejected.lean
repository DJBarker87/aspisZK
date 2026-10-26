import R1Z.ProverRwOuterReservationFailure
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterRejected
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

/-- Actual caller context discharges every layout guard. The only path
premise is the store's concrete rejected reservation and its advanced state. -/
theorem reserve_failure (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize) (s after : S)
    (failure : store.«reserve» s digest attempt.mask_nonce = .ok (false,after)) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
      store attempt hash binding (ProverRwOuterContextModel.context digest attempt.mask_nonce) s =
      .ok (.Err .ReusedMaskNonce,after) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  rw [ProverRwOuterGuardBridge.checked {ops with op12 := @ProverRwOuterMapErr.map_err}]
  exact ProverRwOuterReservationFailure.rejected store attempt hash binding _ s after failure

theorem body_failure (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets) (s after : S)
    (failure : store.«reserve» s digest attempt.mask_nonce = .ok (false,after)) :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    prover.prove_masked_with_attempt store pub compiled v hash
      (ProverRwOuterContextModel.context digest attempt.mask_nonce) binding attempt s =
      .ok (.Err .Semantic,after) :=
  ProverRwOuterReservationFailure.body_failure ops store pub compiled v hash _ binding attempt s after
    (reserve_failure ops store attempt hash binding digest s after failure)

#print axioms reserve_failure
#print axioms body_failure
end R1Z.ProverRwOuterRejected
