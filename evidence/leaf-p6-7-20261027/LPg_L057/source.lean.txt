import LPc_Iteration
import LPa_StageLaws
set_option autoImplicit false
namespace LPg
/-- An actual earlier error prevents all later loop steps from replacing its index. -/
theorem first_error_sticky (bad : Nat → Bool) (n m i : Nat) (hm : n ≤ m)
    (hit : LPa.firstBad bad n = some i) : LPa.firstBad bad m = some i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction d with
  | zero => simpa using hit
  | succ d ih =>
    change (match LPa.firstBad bad (n+d) with
      | some j => some j
      | none => if bad (n+d) then some (n+d) else none) = some i
    rw [ih]
#print axioms first_error_sticky
end LPg
