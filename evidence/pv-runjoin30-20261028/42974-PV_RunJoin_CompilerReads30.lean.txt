import R1Z.PV_RunJoin_ForestEquality30
import R1Z.PV_Src_CompilerTactic
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompilerReads30
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

theorem read_equal (read : Result (Array U32 8#usize)) (d expected : Array U32 8#usize)
    (hr : read = ok d)
    (hc : core.array.equality.PartialEqArray.ne aspis_core.field.M31.Insts.CoreCmpPartialEqM31
      d expected = ok false) : read = ok expected :=
  hr.trans (congrArg Result.ok (PV_RunJoin_ForestEquality30.equal d expected hc))
#print axioms read_equal

theorem lane [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    ∃ records, pair_forest_copy_builder.CopyRecords.new input out recipient change snapshot publicInput.asset = ok records ∧
      pair_forest_copy_builder.CopyRecords.path_digest records 21#usize = ok anchor := by
  rcases publicInput with ⟨pa,pn,pr,pc,asset⟩
  cases pr <;> unfold pair_forest_trace.compile_forest_from_copies at h
  all_goals
    pv_peel h with records hr
    refine ⟨records,hr,?_⟩
    repeat' first
      | (apply read_equal <;> assumption)
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
#print axioms lane

theorem nullifier [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    ∃ records, pair_forest_copy_builder.CopyRecords.new input out recipient change snapshot publicInput.asset = ok records ∧
      pair_forest_copy_builder.CopyRecords.nullifier records = ok publicInput.nullifier := by
  rcases publicInput with ⟨pa,pn,pr,pc,asset⟩
  cases pr <;> unfold pair_forest_trace.compile_forest_from_copies at h
  all_goals
    pv_peel h with records hr
    refine ⟨records,hr,?_⟩
    repeat' first
      | (apply read_equal <;> assumption)
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
#print axioms nullifier

theorem change [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    ∃ records, pair_forest_copy_builder.CopyRecords.new input out recipient change snapshot publicInput.asset = ok records ∧
      pair_forest_copy_builder.CopyRecords.change records = ok publicInput.change_commitment := by
  rcases publicInput with ⟨pa,pn,pr,pc,asset⟩
  cases pr <;> unfold pair_forest_trace.compile_forest_from_copies at h
  all_goals
    pv_peel h with records hr
    refine ⟨records,hr,?_⟩
    repeat' first
      | (apply read_equal <;> assumption)
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
#print axioms change

theorem anchor [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    ∃ records, pair_forest_copy_builder.CopyRecords.new input out recipient change snapshot publicInput.asset = ok records ∧
      pair_forest_copy_builder.CopyRecords.path_digest records 24#usize = ok publicInput.anchor := by
  rcases publicInput with ⟨pa,pn,pr,pc,asset⟩
  cases pr <;> unfold pair_forest_trace.compile_forest_from_copies at h
  all_goals
    pv_peel h with records hr
    refine ⟨records,hr,?_⟩
    repeat' first
      | (apply read_equal <;> assumption)
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
#print axioms anchor
end R1Z.PV_RunJoin_CompilerReads30
