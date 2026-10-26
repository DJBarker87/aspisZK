import R1Z.ProverRwP6BodyGamma
import R1Z.ProverRwBodyCandidateData
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BodyData
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore ProverRwBodyDataCriterion
variable [ExternalTypes]
-- Retarget the complete data criterion to the four installed entries. The
-- remaining whole proof/audit data equation is explicit and is not supplied.
theorem refinement_of_data (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error)) :
    data (ProverRwP6BodyStore.execute ops store pub compiled v hash binding digest attempt s)=model →
      ProverRwP6BodyStore.execute ops store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model := by
  intro same
  apply eq_of_data after
  · exact ProverRwP6BodyStore.writeback ops store pub compiled v hash
      binding digest attempt s after accepted reservation
  · exact ProverRwBodyCandidateData.keeps_withState after model
  · rw [ProverRwBodyCandidateData.data_withState]
    exact same
#print axioms refinement_of_data
end R1Z.ProverRwP6BodyData
