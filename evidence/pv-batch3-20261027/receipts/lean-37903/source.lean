import Aeneas
namespace PV_B3_ShiftCount222
open Aeneas Aeneas.Std
set_option autoImplicit false

-- A Rust usize shift masks the count to the low six bits on the pinned
-- 64-bit target. The backend API accepts U32; its total cast preserves them.
theorem count_mod64 (count : Usize) :
    (UScalar.cast .U32 count).val % 64 = count.val % 64 := by
  rw [UScalar.cast_val_eq]
  change (count.val % 2^32) % 2^6 = count.val % 2^6
  exact Nat.mod_mod_of_dvd _ (by decide)

#print axioms count_mod64
end PV_B3_ShiftCount222
