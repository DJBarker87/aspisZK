import Init.Data.UInt.Bitwise
set_option autoImplicit false
namespace NEK_WordWindows

theorem digits_ext (radix count a b : Nat) (positive : 0 < radix)
    (boundA : a < radix ^ count) (boundB : b < radix ^ count)
    (windows : ∀ i, i < count → a / radix ^ i % radix = b / radix ^ i % radix) : a = b := by
  induction count generalizing a b with
  | zero =>
    have ha : a = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ boundA)
    have hb : b = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ boundB)
    exact ha.trans hb.symm
  | succ k ih =>
    have low : a % radix = b % radix := by simpa using windows 0 (Nat.zero_lt_succ k)
    have qa : a / radix < radix ^ k := (Nat.div_lt_iff_lt_mul positive).2 (by simpa [Nat.pow_succ] using boundA)
    have qb : b / radix < radix ^ k := (Nat.div_lt_iff_lt_mul positive).2 (by simpa [Nat.pow_succ] using boundB)
    have upper : a / radix = b / radix := ih _ _ qa qb (by
      intro i hi
      simpa only [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm] using windows (i+1) (Nat.succ_lt_succ hi))
    calc
      a = a % radix + radix * (a / radix) := (Nat.mod_add_div _ _).symm
      _ = b % radix + radix * (b / radix) := by rw [low, upper]
      _ = b := Nat.mod_add_div _ _

def byteWindow (word : UInt64) (offset : Nat) : UInt64 :=
  (word >>> UInt64.ofNat (8 * offset)) &&& 255

theorem byteWindow_nat (word : UInt64) (offset : Nat) (valid : offset < 8) :
    (byteWindow word offset).toNat = word.toNat / 256 ^ offset % 256 := by
  have small : 8 * offset < 64 := Nat.mul_lt_mul_of_pos_left valid (by decide)
  have rep : (UInt64.ofNat (8 * offset)).toNat = 8 * offset :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans small (by decide : 64 < UInt64.size))
  simp only [byteWindow, UInt64.toNat_and, UInt64.toNat_shiftRight, rep, Nat.mod_eq_of_lt small]
  change (word.toNat >>> (8 * offset)) &&& (2 ^ 8 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem word_windows_ext (actual expected : UInt64)
    (windows : ∀ i, i < 8 → byteWindow actual i = byteWindow expected i) : actual = expected := by
  apply UInt64.toNat_inj.mp
  apply digits_ext 256 8 _ _ (by decide)
  · exact actual.toNat_lt
  · exact expected.toNat_lt
  · intro i hi
    have h := congrArg UInt64.toNat (windows i hi)
    simpa only [byteWindow_nat actual i hi, byteWindow_nat expected i hi] using h

#print axioms digits_ext
#print axioms byteWindow_nat
#print axioms word_windows_ext
end NEK_WordWindows
