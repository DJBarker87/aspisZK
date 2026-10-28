import R1Z.PV_RDCD_Range194
set_option autoImplicit false
namespace R1Z.PV_RDCD_RangeForward
open Aeneas Aeneas.Std Result
abbrev Range := PV_RDCD_Range194.Range
/-- Exact usize TrustedStep forward branch; no arithmetic overflow is reachable. -/
def source (r : Range) : Result (Option Usize × Range) :=
  if h : r.start.val < r.«end».val then
    let next := UScalar.ofNatCore (r.start.val+1) (by have := r.«end».hBounds; omega)
    ok (some r.start, {start:=next, «end»:=r.«end»})
  else ok (none,r)
theorem forward_bound (r : Range) (h : r.start.val < r.«end».val) :
    r.start.val+1 ≤ UScalar.max .Usize := by scalar_tac

theorem next (r : Range) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r = source r := by
  by_cases h : r.start.val < r.«end».val
  · have hb := forward_bound r h
    have hb' : r.start.val < UScalar.max .Usize := by omega
    simp [core.iter.range.IteratorRange.next,core.iter.range.StepUsize,
      core.iter.range.UScalarStep,core.iter.range.UScalarStep.forward_checked,
      core.cmp.impls.PartialOrdUsize.lt,core.clone.CloneUsize,source,h,hb,hb']
  · simp [core.iter.range.IteratorRange.next,core.iter.range.StepUsize,
      core.iter.range.UScalarStep,core.cmp.impls.PartialOrdUsize.lt,source,h]
#print axioms forward_bound
#print axioms next
end R1Z.PV_RDCD_RangeForward
