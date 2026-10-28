import R1Z.PV_RunJoin_ResultMap31
import R1Z.PV_RunJoin_TwoOutputSentinel31
import R1Z.PV_RunJoin_CompilerReads31
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CompilerSentinel31
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

theorem sentinel [ExternalLinear] [Records]
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (recipient : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (change : payment_relation.PoolV1OutputNoteWitnessV1)
    (publicInput : pair_forest_trace.ForestPublic) (anchor : Array U32 8#usize)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1)
    (compiled : pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (expected : Array U32 8#usize) (shape : publicInput.recipient_commitment = some expected)
    (h : pair_forest_trace.compile_forest_from_copies input out recipient change
      publicInput anchor snapshot = ok (.Ok compiled)) :
    Canon8 publicInput.change_commitment ∧ publicInput.change_commitment.val[7]! ≠ 0#u32 := by
  rcases publicInput with ⟨pa,pn,pr,pc,asset⟩
  cases pr with
  | none => cases shape
  | some value =>
    cases Option.some.inj shape
    unfold pair_forest_trace.compile_forest_from_copies at h
    repeat' first
      | exact PV_RunJoin_TwoOutputSentinel31.source _ _ _ hvalue
      | (have he := PV_RunJoin_DecoderReturn29.branch_continue _ _ hvalue; clear hvalue; cases he)
      | (have he := PV_RunJoin_ResultMap31.success _ _ _ _ hvalue; clear hvalue; cases he)
      | (have he := PV_RunJoin_ForestEquality30.equal _ _ hvalue; clear hvalue; cases he)
      | (have _result : core.result.Result _ _ := value; cases value <;> pv_head h)
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
#print axioms sentinel
end R1Z.PV_RunJoin_CompilerSentinel31
