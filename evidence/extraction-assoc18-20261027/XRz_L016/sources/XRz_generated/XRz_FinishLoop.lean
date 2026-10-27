import XRz_FinishBody
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XRz_FinishLoop
open XRx_FinishStep XRz_FinishBody
def fill (f : Nat → Q) : Nat → Nat → Back
 | _,0 => id
 | i,n+1 => fun t => put i (f i) (fill f (i+1) n t)
/-- Arbitrary-length symbolic traversal of the actual finish loop. -/
theorem source (b : verifier.BatchedWeights) (w : Slice Q) (f : Nat → Q)
 (values : ∀ i : Usize, i.val<w.length → verifier.BatchedWeights.value b i=ok (f i.val))
 (n : Nat) (i : Usize) (back : Back) (len : w.length=i.val+n) :
 verifier.BatchedWeights.finish_loop ⟨⟨w,i.val⟩,i⟩ back b=
 ok (fun t => back (fill f i.val n t)) := by
 induction n generalizing i back with
 | zero =>
  unfold verifier.BatchedWeights.finish_loop
  rw [loop.eq_def,XRz_FinishBody.stopped b w i back (by omega)]
  rfl
 | succ n ih =>
  obtain ⟨next,hnext,hbody⟩ := XRz_FinishBody.active b w i back (by omega) (f i.val) (values i (by omega))
  unfold verifier.BatchedWeights.finish_loop
  rw [loop.eq_def,hbody]
  change verifier.BatchedWeights.finish_loop ⟨⟨w,i.val+1⟩,next⟩ (fun t => back (put i.val (f i.val) t)) b = _
  rw [←hnext,ih next (fun t => back (put i.val (f i.val) t)) (by omega)]
  rfl
#print axioms source
end XRz_FinishLoop
