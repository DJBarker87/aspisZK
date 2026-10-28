import R1Z.PV_Join_CodecDictionary
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_CodecCaller
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore ProverRwBodyDataCriterion
variable [ExternalTypes]
-- Same P6 theorem statement after replacing three entries by the exact CB selection.
-- The whole-data equation and reservation premise are retained verbatim.
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
    data (ProverRwBodyNativeWideInstall.execute (PV_Join_CodecDictionary.selected ops) store pub compiled v hash binding digest attempt s)=model →
      ProverRwBodyNativeWideInstall.execute (PV_Join_CodecDictionary.selected ops) store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model := by
  rw [PV_Join_CodecDictionary.dictionary]
  exact ProverRwP6BodyData.refinement_of_data ops store pub compiled v hash
    binding digest attempt s after accepted reservation model
#print axioms refinement_of_data
end R1Z.PV_Join_CodecCaller
