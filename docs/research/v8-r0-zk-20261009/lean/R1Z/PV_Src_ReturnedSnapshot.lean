import R1Z.PV_Src_ForestCompilation

/-! The compiler returns its supplied snapshot on every successful branch.
This discharges the apparent independent-snapshot issue at the successful
caller boundary; no hash or recurrence computation is evaluated. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ReturnedSnapshot
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
open BuilderRecordsFields

theorem returned_snapshot [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic)
    (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    compiled.public_statement.live_snapshot = snapshot := by
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

#print axioms returned_snapshot
end R1Z.PV_Src_ReturnedSnapshot
