import R17MinimalReverseBits
import R17MinimalReverseBitsBridge

set_option autoImplicit false

namespace R17TableExponentDomainBridge

open R17MinimalReverseBits

/-- Exponent encoded by the left table entry at a low nine-bit index. -/
def leftExponent (lo : Nat) : Nat := 2 ^ 10 + 2 ^ 21 * reverseBits 9 lo

/-- Exponent encoded by the right table entry at a high nine-bit index. -/
def rightExponent (hi : Nat) : Nat := 2 ^ 12 * reverseBits 9 hi

/-- The source's two table exponents multiply to the stored 18-bit reversed
index exponent, after the fixed base offset. This is the arithmetic bridge;
literal table-entry correctness remains a separate certificate. -/
theorem pairedTableExponent_eq_stored (lo hi : Nat)
    (hlo : lo < 2 ^ 9) (hhi : hi < 2 ^ 9) :
    leftExponent lo + rightExponent hi =
      2 ^ 10 + 2 ^ 12 *
        AspisV5FriBitReverse.reverseBits 18
          (2 ^ 9 * hi + lo) := by
  rw [R17MinimalReverseBitsBridge.reverseBits18_split_source lo hi hlo hhi]
  change (2 : Nat) ^ 10 + 2 ^ 21 * reverseBits 9 lo +
      2 ^ 12 * reverseBits 9 hi =
    2 ^ 10 + 2 ^ 12 *
      (reverseBits 9 lo * 2 ^ 9 + reverseBits 9 hi)
  have hpow : (2 : Nat) ^ 21 = 2 ^ 12 * 2 ^ 9 := by
    rw [← pow_add]
  rw [hpow, Nat.mul_add]
  ac_rfl

#print axioms pairedTableExponent_eq_stored

end R17TableExponentDomainBridge
