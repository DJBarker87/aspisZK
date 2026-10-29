import R1Z.PV_RDCD3_RangeFold

namespace R1Z.PV_RDCD3_Range194
set_option autoImplicit false
open Aeneas Aeneas.Std Result
abbrev Range := core.ops.range.Range Usize

/-- Owned deployed TrustedStep usize branch, preserving returned iterator state. -/
def source (r : Range) : Result (Option Usize × Range) :=
  if h : r.start.val < r.«end».val then
    let successor := UScalar.ofNatCore (r.start.val+1) (by have := r.«end».hBounds; omega)
    ok (some r.start, {start:=successor, «end»:=r.«end»})
  else ok (none,r)

theorem successor_bound (r : Range) (active : r.start.val < r.«end».val) :
    r.start.val+1 ≤ UScalar.max .Usize := by scalar_tac

/-- Checked extracted Step and deployed unchecked TrustedStep have the same
complete result: no failed checked increment is reachable under the guard. -/
theorem extracted (r : Range) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r = source r := by
  by_cases h : r.start.val < r.«end».val
  · have hb := successor_bound r h
    have hb' : r.start.val < UScalar.max .Usize := by omega
    simp [core.iter.range.IteratorRange.next,core.iter.range.StepUsize,
      core.iter.range.UScalarStep,core.iter.range.UScalarStep.forward_checked,
      core.cmp.impls.PartialOrdUsize.lt,core.clone.CloneUsize,source,h,hb,hb']
  · simp [core.iter.range.IteratorRange.next,core.iter.range.StepUsize,
      core.iter.range.UScalarStep,core.cmp.impls.PartialOrdUsize.lt,source,h]

def project (r : Range) : PV_RDCD3_RangeFold.Cursor := ⟨r.start.val,r.«end».val⟩

def projectResult (x : Option Usize × Range) : Option Nat × PV_RDCD3_RangeFold.Cursor :=
  (x.1.map (fun n => n.val),project x.2)

/-- All endpoints, including empty and reversed ranges; both fields survive. -/
theorem projection (r : Range) :
    (do let out ← source r; ok (projectResult out)) =
      ok (PV_RDCD3_RangeFold.next (project r)) := by
  by_cases h : r.start.val < r.«end».val
  · simp [source,projectResult,project,PV_RDCD3_RangeFold.next,h]
  · simp [source,projectResult,project,PV_RDCD3_RangeFold.next,h]

#print axioms successor_bound
#print axioms extracted
#print axioms projection
end R1Z.PV_RDCD3_Range194
