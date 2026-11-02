import PV_B3P_NthKernelGuard559227
import PV_B3P_Std559KernelFuns227
namespace PV_B3P_NthSource559227
open Aeneas Aeneas.Std core.ops.range PV_B3P_NthKernelGuard559227
set_option autoImplicit false
/-- Source default spec_nth over Usize, with the guarded successor represented
by wrapping_add. The safety proof below shows it cannot wrap. Exhaustion sets
start=end even for an initially reversed range. -/
def source (r : Range Usize) (n : Usize) : Result (Option Usize × Range Usize) := do
  let candidate ← core.iter.range.StepUsize.forward_checked r.start n
  match candidate with
  | none => .ok (none,{r with start := r.end})
  | some item =>
      if item.val < r.end.val then
        .ok (some item,{r with start := Usize.wrapping_add item 1#usize})
      else .ok (none,{r with start := r.end})

theorem clone_value (v : Usize) :
    core.iter.range.StepUsize.cloneInst.clone v = .ok v := rfl

theorem less_value (v w : Usize) :
    core.iter.range.StepUsize.partialOrdInst.lt v w = .ok (decide (v.val < w.val)) := rfl

theorem increment_wrap (item end_ : Usize) (guard : item.val < end_.val) :
    core.iter.range.StepUsize.forward_checked item 1#usize =
      .ok (some (Usize.wrapping_add item 1#usize)) := by
  obtain ⟨next,run,value⟩ := increment_some item end_ guard
  have wrap : (Usize.wrapping_add item 1#usize).val = item.val+1 := by
    rw [Usize.wrapping_add_val_eq]
    exact Nat.mod_eq_of_lt (PV_B3Q_RangeActual.increment_safe ⟨item,end_⟩ guard)
  have same : next = Usize.wrapping_add item 1#usize :=
    UScalar.eq_of_val_eq (value.trans wrap.symm)
  exact same ▸ run

/-- Complete Result equality to the unchanged extracted control. The only
external expect_failed call is eliminated by a proved branch guard. -/
theorem source_binding (r : Range Usize) (n : Usize) :
    source r n =
      PV_B3P_Std559Kernel227.core.ops.range.Range.Insts.CoreIterRangeRangeIteratorImpl.spec_nth
        core.iter.range.StepUsize r n := by
  unfold source PV_B3P_Std559Kernel227.core.ops.range.Range.Insts.CoreIterRangeRangeIteratorImpl.spec_nth
  rw [clone_value,bind_tc_ok]
  apply congrArg (Aeneas.Std.bind _)
  funext candidate
  cases candidate with
  | none => rw [clone_value,bind_tc_ok]
  | some item =>
      simp only [less_value,bind_tc_ok]
      by_cases guard : item.val < r.end.val
      · simp only [guard,decide_true,↓reduceIte]
        rw [clone_value,bind_tc_ok,increment_wrap item r.end guard,bind_tc_ok]
      · simp only [guard,decide_false,Bool.false_eq_true,if_false,clone_value,bind_tc_ok]

#print axioms clone_value
#print axioms less_value
#print axioms increment_wrap
#print axioms source_binding
end PV_B3P_NthSource559227
