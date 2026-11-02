import PV_B3P_Std569KernelFuns227
import PV_B3P_NextFormatting569227
namespace PV_B3P_NextExtraction569227
open Aeneas Aeneas.Std core.ops.range PV_B3P_NthFormattingFinal559227
open PV_B3P_NthSourceFinal559227 PV_B3P_NextFormatting569227
set_option autoImplicit false
/-- Full Result equality to the default extracted next. The handler is arbitrary;
no successful-output premise or formatter semantics enters the statement. -/
theorem source_binding (handler : Str → Result Never) (r : Range Usize) :
    PV_B3P_NextFormatting569227.source handler r =
      PV_B3P_Std569Range227.core.ops.range.Range.Insts.CoreIterRangeRangeIteratorImpl.spec_next
        core.iter.range.StepUsize r := by
  unfold PV_B3P_NextFormatting569227.source
    PV_B3P_Std569Range227.core.ops.range.Range.Insts.CoreIterRangeRangeIteratorImpl.spec_next
  simp only [less_value,bind_tc_ok]
  by_cases guard : r.start.val < r.end.val
  · simp only [guard,decide_true,if_true,increment_value handler r.start r.end guard,
      clone_value,bind_tc_ok,forward_projection]
    rw [increment_wrap_one r.start r.end guard] <;> rfl
  · simp only [guard,decide_false,Bool.false_eq_true,if_false]

theorem extraction_model_binding (r : Range Usize) :
    PV_B3P_Std569Range227.core.ops.range.Range.Insts.CoreIterRangeRangeIteratorImpl.spec_next
      core.iter.range.StepUsize r = PV_B3Q_RangeActual.model r :=
  (source_binding (fun _ => .fail .panic) r).symm.trans (model_binding _ r)
#print axioms source_binding
#print axioms extraction_model_binding
end PV_B3P_NextExtraction569227
