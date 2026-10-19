import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.NatPowAssoc

set_option autoImplicit false

namespace R17MinimalReverseBits

/-- The source definition copied verbatim from AspisV5FriBitReverse.reverseBits. -/
def reverseBits : Nat → Nat → Nat
  | 0, _ => 0
  | width + 1, value =>
      (value % 2) * 2 ^ width + reverseBits width (value / 2)

/-- Fixed-width reversal of a concatenation, proved with natural division and
modulus identities and no reflection or automation. -/
theorem reverseBits_append (w v a b : Nat) (hb : b < 2 ^ w) :
    reverseBits (w + v) (2 ^ w * a + b) =
      reverseBits w b * 2 ^ v + reverseBits v a := by
  induction w generalizing v a b with
  | zero =>
      have hb0 : b < 1 := by simpa using hb
      have hbz : b = 0 := Nat.lt_one_iff.mp hb0
      subst b
      simp [reverseBits]
  | succ w ih =>
      change reverseBits (Nat.succ w + v)
        (2 ^ Nat.succ w * a + b) =
        reverseBits (Nat.succ w) b * 2 ^ v + reverseBits v a
      rw [Nat.succ_add, reverseBits]
      have hpow : 2 ^ Nat.succ w = 2 * 2 ^ w := by
        rw [pow_succ]
        ac_rfl
      let c : Nat := 2 ^ w * a
      have harg : 2 ^ Nat.succ w * a + b = 2 * c + b := by
        calc
          2 ^ Nat.succ w * a + b = (2 * 2 ^ w) * a + b := by rw [hpow]
          _ = 2 * (2 ^ w * a) + b := by ac_rfl
          _ = 2 * c + b := by rfl
      rw [harg, Nat.mul_add_div (Nat.succ_pos 1), Nat.mul_add_mod]
      have hb2 : b / 2 < 2 ^ w := by
        have hbound : b < 2 ^ w * 2 := by
          simpa [pow_succ] using hb
        exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).2 hbound
      rw [ih v a (b / 2) hb2]
      have hrev : reverseBits (Nat.succ w) b =
          (b % 2) * 2 ^ w + reverseBits w (b / 2) := rfl
      rw [hrev, npow_add w v 2, Nat.add_mul]
      ac_rfl

/-- Symbolic exponent relation used by the two nine-bit tables. -/
theorem tableExponent_sum (lo hi : Nat) :
    (2 : Nat) ^ 10 + 2 ^ 21 * reverseBits 9 lo + 2 ^ 12 * reverseBits 9 hi =
      2 ^ 10 + 2 ^ 12 *
        (reverseBits 9 lo * 2 ^ 9 + reverseBits 9 hi) := by
  have hpow : (2 : Nat) ^ 21 = 2 ^ 12 * 2 ^ 9 := by
    rw [← npow_add 12 9 2]
  rw [hpow, Nat.mul_add] <;> ac_rfl

/-- The 18-bit reversal splits into its low-nine and high-nine table indices. -/
theorem reverseBits18_split (lo hi : Nat) (hlo : lo < 2 ^ 9)
    (_hhi : hi < 2 ^ 9) :
    reverseBits 18 (2 ^ 9 * hi + lo) =
      reverseBits 9 lo * 2 ^ 9 + reverseBits 9 hi := by
  exact reverseBits_append 9 9 hi lo hlo

#print axioms reverseBits_append
#print axioms tableExponent_sum
#print axioms reverseBits18_split

end R17MinimalReverseBits
