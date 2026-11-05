import NHC_MarkerTrace
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace NHC_MarkerAny
/-- Vault's nonzero predicate is exactly the complement of marker's zero test. -/
theorem predicate (byte : U8) : decide (byte.val ≠ 0) = !decide (byte.val = 0) := by
  by_cases h : byte.val = 0 <;> simp [h]
#print axioms predicate

theorem any_nonzero (bytes : List U8) :
    bytes.any (fun b => decide (b.val ≠ 0)) = !(NHC_MarkerTrace.run bytes).1 := by
  induction bytes with
  | nil => rfl
  | cons b bs ih =>
    have ih' : bs.any (fun b => !decide (b.val = 0)) = !(NHC_MarkerTrace.run bs).1 := by
      simpa only [ne_eq,decide_not] using ih
    by_cases h : b.val = 0 <;> simp [NHC_MarkerTrace.run,h,ih']
#print axioms any_nonzero
end NHC_MarkerAny
