import R1Z.PV_RunJoin_CompilerReads31
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompilerAppend31
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1
theorem afterstate [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    ∃ records leaf,
      pair_forest_copy_builder.CopyRecords.new input out recipient change snapshot publicInput.asset = ok records ∧
      pair_forest_trace.late_append records snapshot leaf = ok (.Ok compiled.afterstate) := by
  unfold pair_forest_trace.compile_forest_from_copies at h
  pv_peel h with records hr
  refine ⟨records,?_,hr,?_⟩
  repeat' first
    | assumption
    | (pv_peel h with value hvalue)
    | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
    | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
    | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
    | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
    | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
    | (cases h; assumption)
#print axioms afterstate
end R1Z.PV_RunJoin_CompilerAppend31
