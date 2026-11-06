import NJH_BorrowLaws
set_option autoImplicit false
namespace NJH_BorrowCounters
open Aeneas Aeneas.Std Result
/-- No wrap on the canonical successful shared-acquisition domain. -/
theorem acquire_value (x : I64) (lo : 0 ≤ x.val)
    (hi : x.val < 9223372036854775807) :
    (I64.wrapping_add x 1#i64).val = x.val + 1 := by
  rw [I64.wrapping_add_val_eq]
  change (x.val + 1).bmod (2^64) = x.val + 1
  apply Int.bmod_eq_of_le <;> omega
/-- No wrap for a live positive shared guard being dropped. -/
theorem drop_value (x : I64) (lo : 0 < x.val)
    (hi : x.val ≤ 9223372036854775807) :
    (I64.wrapping_sub x 1#i64).val = x.val - 1 := by
  rw [I64.wrapping_sub_val_eq]
  change (x.val - 1).bmod (2^64) = x.val - 1
  apply Int.bmod_eq_of_le <;> omega
#print axioms acquire_value
#print axioms drop_value
end NJH_BorrowCounters
