import R1Z.PV_CB3_SamplerWord
namespace R1Z.PV_CB3_WordBits
open PV_CB3_SamplerWord
set_option autoImplicit false

/-- Exact shift-or arithmetic, including the absence of 64-bit wrap. -/
theorem dividend_bits (prior : BitVec 64) (word : BitVec 32)
    (bound : prior.toNat < radix) :
    (((prior <<< 32) ||| word.setWidth 64).toNat) = dividend prior.toNat word.toNat := by
  have hw := word.isLt
  have shift_bound : prior.toNat * 2 ^ 32 < 2 ^ 64 := by
    unfold radix at bound
    change prior.toNat * 4294967296 < 18446744073709551616
    omega
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth_of_le (by omega), Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt shift_bound]
  rw [Nat.mul_comm prior.toNat, ← Nat.two_pow_add_eq_or_of_lt hw]
  unfold dividend radix
  omega

/-- The narrowing cast in the source division step preserves the quotient
under the internally established remainder invariant. -/
theorem quotient_cast (prior : Nat) (word : BitVec 32) (bound : prior < base) :
    (BitVec.ofNat 32 (dividend prior word.toNat / base)).toNat =
      dividend prior word.toNat / base := by
  have hw : word.toNat < radix := word.isLt
  have h := quotient_word_bound prior word.toNat bound hw
  simpa only [BitVec.toNat_ofNat, radix] using Nat.mod_eq_of_lt h

theorem remainder_cast (prior : Nat) (word : BitVec 32) :
    (BitVec.ofNat 32 (dividend prior word.toNat % base)).toNat =
      dividend prior word.toNat % base := by
  have h := canonical_remainder prior word.toNat
  have hbr : base < radix := by unfold base radix; omega
  simpa only [BitVec.toNat_ofNat, radix] using Nat.mod_eq_of_lt (Nat.lt_trans h hbr)

#print axioms dividend_bits
#print axioms quotient_cast
#print axioms remainder_cast
end R1Z.PV_CB3_WordBits
