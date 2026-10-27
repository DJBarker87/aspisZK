import LPa_CanonicalAdd
open Aeneas Aeneas.Std
set_option autoImplicit false
namespace LPa.Add
-- Independent u64/Nat reference formula used by native K020.
theorem word_val_canonical (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
    (word a b).val = if 2147483647 ≤ a.val+b.val
      then a.val+b.val-2147483647 else a.val+b.val := by
  have nowrap : a.val+b.val < 4294967296 := by omega
  have sum : (U32.wrapping_add a b).val = a.val+b.val := by
    change (a.bv+b.bv).toNat = a.bv.toNat+b.bv.toNat
    exact BitVec.toNat_add_of_lt nowrap
  dsimp only [word]
  by_cases h : 2147483647 ≤ a.val+b.val
  · have guard : U32.wrapping_add a b ≥ 2147483647#u32 := by
      change 2147483647 ≤ (U32.wrapping_add a b).val
      rw [sum]
      exact h
    rw [if_pos guard, if_pos h]
    change ((a.bv+b.bv)-(2147483647#u32).bv).toNat = a.val+b.val-2147483647
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      change 2147483647 ≤ (U32.wrapping_add a b).val
      rw [sum]
      exact h)]
    change (U32.wrapping_add a b).val-2147483647 = _
    rw [sum]
  · have guard : ¬ U32.wrapping_add a b ≥ 2147483647#u32 := by
      change ¬ 2147483647 ≤ (U32.wrapping_add a b).val
      rw [sum]
      exact h
    rw [if_neg guard, if_neg h]
    exact sum

#print axioms word_val_canonical
end LPa.Add
