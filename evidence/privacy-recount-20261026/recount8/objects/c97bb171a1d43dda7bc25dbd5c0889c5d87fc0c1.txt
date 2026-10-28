import R1Z.PV_RunJoin_DecoderReturn29
import R1Z.PV_RunJoin_CompilerReads30
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LateAppendRoot31
open Aeneas Aeneas.Std Result BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

theorem root [ExternalLinear]
    (records : pair_forest_copy_builder.CopyRecords)
    (snapshot : pair_tree_profile.PoolV1PairLiveSnapshotV1) (leaf : Array U32 8#usize)
    (afterstate : pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (h : pair_forest_trace.late_append records snapshot leaf = ok (.Ok afterstate)) :
    pair_forest_copy_builder.CopyRecords.append_root records = ok afterstate.next_root := by
  unfold pair_forest_trace.late_append at h
  split at h
  · cases h
  · repeat' first
      | (have he := PV_RunJoin_DecoderReturn29.branch_continue _ _ hvalue; clear hvalue; cases he)
      | (have _result : core.result.Result _ _ := value; cases value <;> pv_head h)
      | (apply PV_RunJoin_CompilerReads30.read_equal <;> assumption)
      | (pv_peel h with value hvalue)
      | exact False.elim (PV_Src_ResultControl.error_ne_ok _ _ h)
      | exact False.elim (PV_Src_ResultControl.same_residual_ne_ok _ _ h)
      | (have _test : Bool := value; cases value <;> simp only [Bool.false_eq_true,↓reduceIte] at h)
      | (have _test : core.ops.control_flow.ControlFlow _ _ := value; cases value)
      | (have _test : _ × _ := value; rcases value with ⟨value,rest⟩)
      | (cases h; apply PV_RunJoin_CompilerReads30.read_equal <;> assumption)
#print axioms root
end R1Z.PV_RunJoin_LateAppendRoot31
