import AspisR1FastDotsCurrent.FunsOpsV4
import Aeneas.Std.RangeIter
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsStepSchedule
abbrev Range := core.ops.range.Range Usize
abbrev StepBy := core.iter.adapters.step_by.StepBy Range
def startRange : Range := { start := 0#usize, «end» := 26#usize }
def startBy : StepBy := { iter := startRange, step_by := 4#usize }
theorem initialized_step_by :
  core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    startRange 4#usize = .ok startBy := by
  simp [startBy, startRange, core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default]
theorem next_profile (it : StepBy) (hstart : it.iter.start.val < it.iter.end.val)
    (hstep : it.step_by.val > 0)
    (hstep_in_range : it.iter.start.val + it.step_by.val ≤ it.iter.end.val) :
  core.iter.adapters.step_by.IteratorStepBy.next
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) it
    ⦃ (opt : Option Usize) (it' : StepBy) =>
      opt = some it.iter.start ∧
      it'.iter.start.val = it.iter.start.val + it.step_by.val ∧
      it'.iter.end = it.iter.end ∧ it'.step_by = it.step_by ⦄ := by
  exact core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_some_spec
    it hstart hstep hstep_in_range
#print axioms initialized_step_by
#print axioms next_profile
end AspisR1FastDotsStepSchedule
