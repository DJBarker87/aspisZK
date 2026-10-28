import R1Z.PV_RDCD_Index194
set_option autoImplicit false
namespace R1Z.PV_RDCD_Range194
open Aeneas Aeneas.Std Result
abbrev Range := core.ops.range.Range Usize
/-- Deployed TrustedStep usize branch: subtraction is reached only with end>start. -/
def backward (r : Range) : Result (Option Usize × Range) :=
  if h : r.start.val < r.«end».val then
    let last := UScalar.ofNatCore (r.«end».val-1) (by have := r.«end».hBounds; omega)
    ok (some last, {start:=r.start, «end»:=last})
  else ok (none,r)
/-- Both the unchecked native subtraction and checked library model are in range. -/
theorem backward_bound (r : Range) (h : r.start.val < r.«end».val) :
    1 ≤ r.«end».val ∧ r.start.val ≤ r.«end».val-1 := by omega

theorem next_back (r : Range) :
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back core.iter.range.StepUsize r = backward r := by
  by_cases h : r.start.val < r.«end».val
  · have hb : 1 ≤ r.«end».val := (backward_bound r h).1
    simp [core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepUsize,core.iter.range.UScalarStep,
    core.iter.range.UScalarStep.backward_checked,backward, core.cmp.impls.PartialOrdUsize.lt,h,hb]
  · simp [core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
      core.iter.range.StepUsize,core.iter.range.UScalarStep,backward,
      core.cmp.impls.PartialOrdUsize.lt,h]

theorem reverse_dispatch (r : core.iter.adapters.rev.Rev Range) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) r = (do
        let next ← backward r.iter
        ok (next.1,⟨next.2⟩)) := by
  simp only [core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.DoubleEndedIterator,next_back]

theorem reverse_new (r : Range) :
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) r = ok ⟨r⟩ := rfl
#print axioms backward_bound
#print axioms next_back
#print axioms reverse_dispatch
#print axioms reverse_new
end R1Z.PV_RDCD_Range194
