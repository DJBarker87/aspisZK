import R1Z.PV_OWNK_ReduceNat
set_option autoImplicit false
namespace R1Z.PV_OWNK_ReduceBits
open PV_OWNK_ReduceNat
def fold64 (x : BitVec 64) : BitVec 64 := (x &&& 2147483647#64) + (x >>> 31)
def word (x : BitVec 64) : BitVec 32 := (fold64 (fold64 x)).setWidth 32
def reduced (x : BitVec 64) : BitVec 32 :=
 word x - (2147483647#32 &&& (0#32 - (if (2147483647#32).ule (word x) then 1#32 else 0#32)))
theorem fold_val (x : BitVec 64) : (fold64 x).toNat = fold31 x.toNat := by
 have hb := first_bound x.toNat x.isLt
 have he : (fold64 x).toNat = fold31 x.toNat % 18446744073709551616 := by
  simp only [fold64,BitVec.toNat_add,BitVec.toNat_and,BitVec.toNat_ushiftRight,
   Nat.shiftRight_eq_div_pow]
  change ((x.toNat &&& (2^31-1)) + x.toNat / 2147483648) % 18446744073709551616 = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl
 rw [he,Nat.mod_eq_of_lt (by omega)]
theorem word_val (x : BitVec 64) : (word x).toNat = fold31 (fold31 x.toNat) := by
 have hb := second_bound _ (first_bound x.toNat x.isLt)
 rw [word,BitVec.toNat_setWidth,fold_val,fold_val]
 exact Nat.mod_eq_of_lt (by omega)
theorem reduced_val (x : BitVec 64) : (reduced x).toNat = reduce64 x.toNat := by
 have hw := word_val x
 have hb := second_bound _ (first_bound x.toNat x.isLt)
 by_cases h : 2147483647 ≤ (word x).toNat
 · simp only [reduced,BitVec.ule,show (2147483647#32).toNat = 2147483647 from rfl,
    h,decide_true,if_pos]
   change (word x - 2147483647#32).toNat = _
   rw [BitVec.toNat_sub_of_le (show 2147483647#32 ≤ word x from h)]
   change (word x).toNat - 2147483647 = _
   rw [hw]
   unfold reduce64 subtractP P
   rw [if_pos (by omega)]
 · simp only [reduced,BitVec.ule,show (2147483647#32).toNat = 2147483647 from rfl,
    h,decide_false,if_neg]
   change (word x - 0#32).toNat = _
   rw [BitVec.sub_zero,hw]
   unfold reduce64 subtractP P
   rw [if_neg (by omega)]
theorem decode (x : BitVec 64) : (reduced x).toNat = x.toNat % 2147483647 := by
 rw [reduced_val,exact_mod x.toNat x.isLt]
 rfl
#print axioms fold_val
#print axioms word_val
#print axioms reduced_val
#print axioms decode
end R1Z.PV_OWNK_ReduceBits
