import R1Z.PV_Join_Wire_Dictionary
import R1Z.PV_Join_ProofClosure
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_Wire_Caller
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore ProverRwBodyDataCriterion
abbrev native := PV_Join_Wire_Selection.native
-- Organisation of proved source laws, not discharge of the reservation or data equation.
theorem refinement_of_data (base : ExternalTypes) (ops : @ExternalFuns (native base)) :
    letI : ExternalTypes := native base
    ∀ {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce = ok (accepted,after))
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error)),
    data (ProverRwBodyNativeWideInstall.execute (PV_Join_Wire_Selection.selected base ops) store pub compiled v hash binding digest attempt s)=model →
      ProverRwBodyNativeWideInstall.execute (PV_Join_Wire_Selection.selected base ops) store pub compiled v hash binding digest attempt s =
        ProverRwBodyCandidateData.withState after model := by
  letI : ExternalTypes := native base
  intro S store pub compiled v hash binding digest attempt s after accepted reservation model same
  rw [PV_Join_Wire_Dictionary.dictionary] at same ⊢
  apply eq_of_data after
  · exact ProverRwBodyReservationTransport.body_writeback
      (PV_Join_Wire_Dictionary.raw base ops) store pub compiled v hash
      binding digest attempt s after accepted reservation
  · exact ProverRwBodyCandidateData.keeps_withState after model
  · rw [ProverRwBodyCandidateData.data_withState]
    exact same
#print refinement_of_data
#print axioms refinement_of_data
end R1Z.PV_Join_Wire_Caller
#join_closure R1Z.PV_Join_AggregateCaller.refinement_of_data
#join_closure R1Z.PV_Join_Wire_Caller.refinement_of_data
