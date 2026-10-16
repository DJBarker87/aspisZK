import Aeneas

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1TerminalAmountGuardSlice

/-- Exact generated closure body from the pinned terminal candidate Funs
(SHA 04fc129bbd54c8792d5c11e6c017e810cfc68d7a4a9577eca9455088ed04a42e,
lines 3081–3092), isolated so its range consequence can be proved without
importing the entire caller cone. -/
def amount_guard_call_once (_closure : Unit) (amount : Std.U32) : Result Bool := do
  if amount = 0#u32 then ok true
  else
    let limit ← 1#u32 <<< 30#i32
    ok (amount >= limit)

theorem false_implies_amount_range (amount : Std.U32)
    (h : amount_guard_call_once () amount = ok false) :
    0 < amount.val ∧ amount.val < 2 ^ 30 := by
  unfold amount_guard_call_once at h
  by_cases hz : amount = 0#u32
  · simp [hz] at h
  · simp only [hz, if_false, bind_tc_ok] at h
    have hlimit : (1#u32 <<< 30#i32) = ok 1073741824#u32 := by rfl
    rw [hlimit] at h
    simp only [bind_tc_ok] at h
    have hpositive : amount.val ≠ 0 := by
      intro hv
      exact hz (UScalar.eq_of_val_eq hv)
    have hupper : ¬ 1073741824#u32 ≤ amount := by
      simpa using h
    constructor
    · omega
    · change ¬ 1073741824 ≤ amount.val at hupper
      exact Nat.lt_of_not_ge hupper

#print axioms false_implies_amount_range
end AspisR1TerminalAmountGuardSlice
