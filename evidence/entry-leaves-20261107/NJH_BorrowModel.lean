import NJH_BorrowCounters
set_option autoImplicit false
namespace NJH_BorrowModel
open Aeneas Aeneas.Std Result
def observe : core.result.Result I64 Unit → Option Int
  | .Ok n => some n.val
  | .Err _ => none
def shared (n : Int) : Option Int :=
  if 0 ≤ n ∧ n < 9223372036854775807 then some (n+1) else none
/-- Complete extracted scalar acquisition reply equals its integer law.
This observes the counter carrier only, not SDK heap or Ref provenance. -/
theorem shared_exact (x : I64) :
    (do let r ← NJH_Ref.shared_ref x; ok (observe r)) = ok (shared x.val) := by
  by_cases lo : x ≥ 0#i64
  · have hlo : 0 ≤ x.val := by simpa using lo
    by_cases hi : x < core.num.I64.MAX
    · have hhi : x.val < 9223372036854775807 := by
        change x.val < 9223372036854775807 at hi
        exact hi
      rw [NJH_BorrowLaws.shared_ok x lo hi]
      simp [observe, shared, hlo, hhi, NJH_BorrowCounters.acquire_value x hlo hhi]
    · have hhi : ¬ x.val < 9223372036854775807 := by
        change ¬ x.val < 9223372036854775807 at hi
        exact hi
      rw [NJH_BorrowLaws.shared_saturated x lo hi]
      simp [observe, shared, hhi]
  · have hlo : ¬ 0 ≤ x.val := by simpa using lo
    rw [NJH_BorrowLaws.shared_negative x lo]
    simp [observe, shared, hlo]
/-- Live shared-guard cleanup has precisely the integer decrement. -/
theorem shared_drop (x : I64) (lo : 0 < x.val)
    (hi : x.val ≤ 9223372036854775807) :
    ∃ y, NJH_Ref.shared_drop_ref x = ok y ∧ y.val = x.val - 1 :=
  ⟨I64.wrapping_sub x 1#i64,rfl,NJH_BorrowCounters.drop_value x lo hi⟩
#print axioms shared_exact
#print axioms shared_drop
end NJH_BorrowModel
