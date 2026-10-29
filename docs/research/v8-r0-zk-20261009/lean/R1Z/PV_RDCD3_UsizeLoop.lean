import R1Z.PV_RDCD3_Range194
import R1Z.PV_RDCD3_RangeLoop

namespace R1Z.PV_RDCD3_UsizeLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
abbrev Range := core.ops.range.Range Usize

def body {S : Type} (f : S → Nat → Result S) (state : Range × S) :
    Result (ControlFlow (Range × S) S) := do
  let (o,r) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize state.1
  match o with
  | none => ok (done state.2)
  | some i => do let acc ← f state.2 i.val; ok (cont (r,acc))

def source {S : Type} (f : S → Nat → Result S) (r : Range) (acc : S) : Result S :=
  loop (body f) (r,acc)

/-- Concrete usize iteration, with complete callback failure and divergence,
refines the ordered recurrence for every valid endpoint pair. -/
theorem complete {S : Type} (f : S → Nat → Result S) (fuel : Nat)
    (r : Range) (acc : S) (bound : r.«end».val = r.start.val+fuel) :
    source f r acc = PV_RDCD3_RangeFold.ordered f fuel r.start.val acc := by
  induction fuel generalizing r acc with
  | zero =>
    have h : ¬r.start.val < r.«end».val := by omega
    rw [source,loop.eq_def]
    simp only [body,PV_RDCD3_Range194.extracted,PV_RDCD3_Range194.source,dif_neg h,bind_tc_ok,PV_RDCD3_RangeFold.ordered]
  | succ fuel ih =>
    have h : r.start.val < r.«end».val := by omega
    rw [source,loop.eq_def]
    simp only [body,PV_RDCD3_Range194.extracted,PV_RDCD3_Range194.source,dif_pos h,bind_tc_ok,PV_RDCD3_RangeFold.ordered]
    cases hf : f acc r.start.val with
    | fail e => simp [hf]
    | div => simp [hf]
    | ok out =>
      simp only [hf,bind_tc_ok]
      apply ih
      simpa using (show r.«end».val = (r.start.val+1)+fuel from by omega)

#print axioms complete
end R1Z.PV_RDCD3_UsizeLoop
