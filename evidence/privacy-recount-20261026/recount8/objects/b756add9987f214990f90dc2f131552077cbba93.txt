import R1Z.ProverRwSuccessErrorInstall
import R1Z.ProverRwBodyCandidateStore
import R1Z.ProverRwBodyDataCriterion
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwBodyErrorData
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore ProverRwBodyDataCriterion

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterGuardLeaves.selected (ProverRwSuccessErrorInstall.selected ops)
theorem heap_installed (ops : ExternalFuns) {T : Type} (copy : core.marker.Copy T)
    (n : Usize) (value : T) :
    (selected ops).op81 copy n value =
      @ProverRwSuccessHeapSource.aspis_core.r0.heap.filled _
        (ProverRwSuccessBodyInterpretation.selected ops) T copy n value := rfl
theorem error_installed (ops : ExternalFuns) (a b : r1_wire.Error) :
    (selected ops).op256 a b=ProverRwSuccessErrorInstall.Src a b := rfl
#print axioms heap_installed
#print axioms error_installed

def withState {A S : Type} (after : S) : Result A → Result (A × S)
  | .ok a => .ok (a,after)
  | .fail e => .fail e
  | .div => .div

theorem data_withState {A S : Type} (after : S) (model : Result A) :
    data (withState after model)=model := by cases model <;> rfl

theorem keeps_withState {A S : Type} (after : S) (model : Result A) :
    Keeps after (withState after model) := by cases model <;> trivial

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
    letI : ExternalFuns := selected ops
    let actual := prover.prove_masked_with_attempt store pub compiled v hash
      (ProverRwOuterContextModel.context digest attempt.mask_nonce) binding attempt s
    data actual=model → actual=withState after model := by
  letI : ExternalFuns := selected ops
  dsimp only
  intro same
  apply eq_of_data after
  · exact ProverRwBodyReservationTransport.body_writeback (ProverRwSuccessErrorInstall.selected ops) store pub compiled v hash
      binding digest attempt s after accepted reservation
  · exact keeps_withState after model
  · rw [data_withState]
    exact same
#print axioms data_withState
#print axioms keeps_withState
#print axioms refinement_of_data
end R1Z.ProverRwBodyErrorData
