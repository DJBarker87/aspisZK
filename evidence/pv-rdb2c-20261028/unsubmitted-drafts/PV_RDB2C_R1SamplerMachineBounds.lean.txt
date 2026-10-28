import R1Z.PV_RDB2C_R1SamplerLongDivision
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Concrete Nat bounds for the sampler's chosen radix and modulus.
These lemmas do not identify Nat operations with Rust machine operations. -/

set_option autoImplicit false

namespace AspisR1.SamplerMachineBounds

def P : Nat := 2^31 - 1
def B : Nat := 2^32

theorem P_pos : 0 < P := by norm_num [P]
theorem B_pos : 0 < B := by norm_num [B]

theorem P_times_B_lt_two63 : P * B < 2^63 := by norm_num [P, B]

/-- The multiply-add in one radix digit is strictly below the signed-bit
boundary, so it also fits in an unsigned 64-bit word. -/
theorem dividend_lt_two63 {r digit : Nat} (hr : r < P) (hdigit : digit < B) :
    r * B + digit < 2^63 := by
  have hstep := AspisR1.SamplerLongDivision.dividend_lt_mul
    (radix := B) (divisor := P) (remainder := r) (digit := digit)
    B_pos P_pos hr hdigit
  exact lt_trans hstep P_times_B_lt_two63

/-- One base-P long-division quotient is a single radix digit. -/
theorem dividend_quotient_lt_B {r digit : Nat} (hr : r < P) (hdigit : digit < B) :
    (r * B + digit) / P < B := by
  simpa [AspisR1.SamplerLongDivision.dividend, B, P] using
    (AspisR1.SamplerLongDivision.quotient_lt_radix
      (radix := B) (divisor := P) (remainder := r) (digit := digit)
      B_pos P_pos hr hdigit)

theorem dividend_remainder_lt_P {r digit : Nat} :
    (r * B + digit) % P < P := by
  simpa [AspisR1.SamplerLongDivision.dividend, B, P] using
    (AspisR1.SamplerLongDivision.remainder_lt_divisor
      (radix := B) (divisor := P) (remainder := r) (digit := digit) P_pos)

/-- Since a 256-bit input is less than 257 blocks of size P^8, its quotient
by P^8 is at most 256. -/
theorem rank_div_P8_le_256 {x : Nat} (hx : x < 2^256) : x / P^8 ≤ 256 := by
  have hP8 : 0 < P^8 := by norm_num [P]
  have h257 : x / P^8 < 257 := by
    apply (Nat.div_lt_iff_lt_mul hP8).2
    calc
      x < 2^256 := hx
      _ < 257 * P^8 := by norm_num [P]
  omega

theorem rank_quotient_plus_one_le_257 {x : Nat} (hx : x < 2^256) :
    x / P^8 + 1 ≤ 257 := by
  have h := rank_div_P8_le_256 hx
  omega

theorem two_le_P8 : 2 ≤ P^8 := by norm_num [P]

theorem rank_div_P8_lt_P8_sub_one {x : Nat} (hx : x < 2^256) :
    x / P^8 < P^8 - 1 := by
  have hquot := rank_div_P8_le_256 hx
  have hlarge : 257 < P^8 := by norm_num [P]
  omega

theorem two_fifty_seven_lt_P : 257 < P := by norm_num [P]

/-- A digit plus the largest accumulator addend still fits in one u32. -/
theorem digit_addend_lt_B {digit addend : Nat}
    (hdigit : digit < P) (haddend : addend ≤ 257) : digit + addend < B := by
  have hcap : P + 257 < B := by norm_num [P, B]
  omega

/-- Adding at most 257 to a base-P digit creates at most one carry. -/
theorem digit_addend_quotient_le_one {digit addend : Nat}
    (hdigit : digit < P) (haddend : addend ≤ 257) :
    (digit + addend) / P ≤ 1 := by
  have hP : 0 < P := P_pos
  have htwoP : digit + addend < 2 * P := by
    have hcap : P + 257 < 2 * P := by norm_num [P]
    omega
  have hquot : (digit + addend) / P < 2 := by
    apply (Nat.div_lt_iff_lt_mul hP).2
    simpa [Nat.mul_comm] using htwoP
  omega

/-- The ordinary subsequent carry addend is included in the general bound. -/
theorem digit_carry_quotient_le_one {digit carry : Nat}
    (hdigit : digit < P) (hcarry : carry ≤ 1) :
    (digit + carry) / P ≤ 1 := by
  apply digit_addend_quotient_le_one hdigit
  omega

#print axioms dividend_lt_two63
#print axioms dividend_quotient_lt_B
#print axioms dividend_remainder_lt_P
#print axioms rank_div_P8_le_256
#print axioms rank_quotient_plus_one_le_257
#print axioms two_le_P8
#print axioms rank_div_P8_lt_P8_sub_one
#print axioms two_fifty_seven_lt_P
#print axioms digit_addend_lt_B
#print axioms digit_addend_quotient_le_one
#print axioms digit_carry_quotient_le_one

end AspisR1.SamplerMachineBounds
