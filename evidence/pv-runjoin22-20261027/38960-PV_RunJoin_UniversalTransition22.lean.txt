import R1Z.PV_Src_ReturnedSnapshot
import R1Z.PV_Src_NativeInput
set_option autoImplicit false
namespace R1Z.PV_RunJoin_UniversalTransition22
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1 BuilderRecordsFields

/-- Every successful branch returns the same afterstate in the trace and in
its public statement. The proof splits symbolic outer control flow only. -/
theorem afterstate [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    compiled.public_statement.candidate_afterstate = compiled.trace.afterstate := by
  rcases publicInput with ⟨pubAnchor,pubNullifier,pubRecipient,pubChange,pubAsset⟩
  cases pubRecipient <;> unfold pair_forest_trace.compile_forest_from_copies at h
  all_goals
    repeat' first
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true, ↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
      | (cases h; rfl)
#print axioms afterstate

/-- Full source transition, including every snapshot and afterstate field,
for every successful native input. No fixtures or whole-run reduction. -/
theorem transition [ExternalLinear] [Records]
    (i : PV_Src_NativeInput.Input)
    (h : PV_Src_NativeInput.run i = ok (.Ok i.compiled)) :
    PV_Src_NativeInput.transition i.compiled.public_statement =
      { live_snapshot := {
          pool := i.snapshot.pool, deployment_domain := i.snapshot.deployment_domain,
          sequence := i.snapshot.sequence, next_pair_index := i.snapshot.next_pair_index,
          current_root := i.snapshot.current_root, frontier := i.snapshot.frontier },
        candidate_afterstate := {
          next_pair_index := i.compiled.trace.afterstate.next_pair_index,
          next_root := i.compiled.trace.afterstate.next_root,
          next_frontier := i.compiled.trace.afterstate.next_frontier } } := by
  have hs := PV_Src_ReturnedSnapshot.returned_snapshot i.witness
    (PV_Src_NativeInput.outputValue i.request) (PV_Src_NativeInput.recipient i.request)
    i.change (PV_Src_NativeInput.forestPublic i.request) i.laneAnchor i.snapshot i.compiled h
  have ha := afterstate i.witness (PV_Src_NativeInput.outputValue i.request)
    (PV_Src_NativeInput.recipient i.request) i.change
    (PV_Src_NativeInput.forestPublic i.request) i.laneAnchor i.snapshot i.compiled h
  unfold PV_Src_NativeInput.transition
  rw [hs,ha]
#print axioms transition
end R1Z.PV_RunJoin_UniversalTransition22
