import Aeneas.Std.Primitives

/-! The generated mixing-row closure returns an owned field value and a
borrow write-back. This leaf proves how that particular write-back closes;
it does not erase arbitrary closure write-backs or certify iterator collect.
The marked body is checked against the pinned actual-source extraction. -/
namespace AspisV8R17.MaskClosureWriteback
open Aeneas.Std Result

variable {K : Type}

-- SOURCE BODY: only field.QM31.mul is abstracted as mul.
def powerCallMut (mul : K → K → Result K) (c : K × K) :
    Result (K × (K × K) × ((K × K) → (K × K))) := do
  let (out, q) := c
  let q1 ← mul out q
  let back := fun c1 => let (q2, _) := c1
                        (q2, q)
  ok (out, (q1, q), back)
-- END SOURCE BODY

/-- End the mutable call's borrow before exposing its updated state. -/
def finishCall {F B : Type} (call : Result (B × F × (F → F))) :
    Result (B × F) := do
  let (value, updated, back) ← call
  ok (value, back updated)

/-- Closing this source closure retains the multiplied power AND fixed node.
Failure and divergence are preserved, not converted into successful values. -/
theorem powerCallMut_closed (mul : K → K → Result K) (power node : K) :
    finishCall (powerCallMut mul (power, node)) = (do
      let next ← mul power node
      ok (power, (next, node))) := by
  cases h : mul power node <;> simp [finishCall, powerCallMut, h]

theorem powerCallMut_success (mul : K → K → Result K) (power node next : K)
    (h : mul power node = ok next) :
    finishCall (powerCallMut mul (power, node)) = ok (power, (next, node)) := by
  rw [powerCallMut_closed, h]
  rfl

/-- A general backward function cannot be discarded: this is a negative
regression against replacing finishCall with the raw updated state. -/
theorem cannot_discard_writeback :
    finishCall (ok (0, 1, fun (_ : Nat) => 2)) ≠
      (ok (0, 1) : Result (Nat × Nat)) := by
  simp [finishCall]

#print axioms powerCallMut_closed
#print axioms powerCallMut_success
#print axioms cannot_discard_writeback
end AspisV8R17.MaskClosureWriteback
