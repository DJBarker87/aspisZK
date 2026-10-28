import R1Z.ProverRwBodyCandidateStore
import R1Z.ProverRwBodyDataCriterion
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwBodyCandidateData
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore ProverRwBodyDataCriterion

def withState {A S : Type} (after : S) : Result A → Result (A × S)
  | .ok a => .ok (a,after)
  | .fail e => .fail e
  | .div => .div

theorem data_withState {A S : Type} (after : S) (model : Result A) :
    data (withState after model)=model := by cases model <;> rfl

theorem keeps_withState {A S : Type} (after : S) (model : Result A) :
    Keeps after (withState after model) := by cases model <;> trivial

variable [ExternalTypes]
-- The proof/audit data equality remains explicit; returned store transport is
-- discharged by the retained reservation/body proof, not assumed separately.
theorem refinement_of_data (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce=.ok (accepted,after))
    (model : Result (core.result.Result ((alloc.vec.Vec U8) × prover.MaskedFixtureAudit) verifier.Error)) :
    letI : ExternalFuns := ProverRwBodyCandidateStore.selected ops
    let actual := prover.prove_masked_with_attempt store pub compiled v hash
      (ProverRwOuterContextModel.context digest attempt.mask_nonce) binding attempt s
    data actual=model → actual=withState after model := by
  letI : ExternalFuns := ProverRwBodyCandidateStore.selected ops
  dsimp only
  intro same
  apply eq_of_data after
  · exact ProverRwBodyCandidateStore.writeback ops store pub compiled v hash
      binding digest attempt s after accepted reservation
  · exact keeps_withState after model
  · rw [data_withState]
    exact same
#print axioms data_withState
#print axioms keeps_withState
#print axioms refinement_of_data
end R1Z.ProverRwBodyCandidateData
