import PV_B3_MaskSparseScalar
namespace PV_B3_MaskSparseBit
open Aeneas Aeneas.Std PV_B3_MaskSparseStep
set_option autoImplicit false

theorem low_value (p : Usize) : (p &&& 15#usize).val = p.val % 16 := by
  change (p.bv &&& (15#usize).bv).toNat = _
  simp only [BitVec.toNat_and]
  change p.val &&& 15 = _
  exact Nat.and_two_pow_sub_one_eq_mod p.val 4

theorem shift_value (p : Usize) :
    (UScalar.cast .U32 (p &&& 15#usize)).val = p.val % 16 := by
  have small : (p &&& 15#usize).val < 16 := by rw [low_value]; omega
  rw [UScalar.cast_val_mod_pow_of_inBounds_eq .U32 _ (by
    change (p &&& 15#usize).val < 4294967296; omega), low_value]

theorem bit_value (p : Usize) : (bit p).val = 2^(p.val % 16) := by
  unfold bit U16.wrapping_shl UScalar.wrapping_shl
  change (((1#u16).bv <<< ((UScalar.cast .U32 (p &&& 15#usize)).val % 16)).toNat) = _
  rw [shift_value, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
  simp only [BitVec.toNat_shiftLeft]
  change (1 <<< (p.val % 16)) % 65536 = _
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  apply Nat.mod_eq_of_lt
  have h : p.val % 16 < 16 := Nat.mod_lt _ (by decide)
  exact Nat.pow_lt_pow_right (by decide) h

theorem mark_value (m : Nat → U16) (p : Usize) (k : Nat) :
    (mark m p k).val =
      if k = p.val / 16 then (m k).val ||| 2^(p.val % 16) else (m k).val := by
  unfold mark
  rw [PV_B3_MaskSparseScalar.block_value]
  by_cases hk : k = p.val / 16
  · subst k
    rw [Function.update_self, if_pos rfl]
    change ((m (p.val / 16)).bv ||| (bit p).bv).toNat = _
    simp only [BitVec.toNat_or, UScalar.bv_toNat, bit_value]
  · rw [Function.update_of_ne hk, if_neg hk]

#print axioms mark_value
#print axioms low_value
#print axioms shift_value
#print axioms bit_value
end PV_B3_MaskSparseBit
