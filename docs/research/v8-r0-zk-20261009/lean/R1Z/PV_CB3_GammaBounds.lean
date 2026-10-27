import R1Z.PV_CB3_RankBound
import R1Z.PV_CB3_GammaRank
import R1Z.PV_CB3_SamplerWord
namespace R1Z.PV_CB3_GammaBounds
open PV_CB3_SamplerCarry PV_CB3_SamplerWord
set_option autoImplicit false

/-- Exponent comparison replaces normalization of the concrete 248-bit power. -/
theorem power_separation (b n : Nat) (large : 3 ≤ b) (many : 2 ≤ n) :
    b < b ^ n - 1 := by
  have hp : b ^ 2 ≤ b ^ n := Nat.pow_le_pow_right (by omega) many
  have hm := Nat.mul_le_mul_left b large
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at hp
  omega

theorem high_small (words : List Nat) (length : words.length = 8)
    (canonical : ∀ d, d ∈ words → d < radix) :
    value radix words / base ^ 8 < base := by
  have h := PV_CB3_RankBound.high_lt_base base radix 3 (by unfold base; omega)
    words canonical (by unfold radix base; omega)
    (by rw [length]; decide)
  simpa only [length] using h

theorem carry_bound (words : List Nat) (length : words.length = 8)
    (canonical : ∀ d, d ∈ words → d < radix) :
    value radix words / base ^ 8 < base ^ 8 - 1 :=
  Nat.lt_trans (high_small words length canonical)
    (power_separation base 8 (by unfold base; omega) (by omega))

/-- Complete mathematical sampler equation with no rank or output premise:
the only inputs are eight machine words. -/
theorem rank_formula (words : List Nat) (length : words.length = 8)
    (canonical : ∀ d, d ∈ words → d < radix) :
    value base (PV_CB3_GammaRank.sampleDigits base radix 8 words) =
      value radix words % (base ^ 8 - 1) + 1 := by
  apply PV_CB3_GammaRank.sample_value base radix 8 (by unfold base; omega) words
  · have hp := power_separation base 8 (by unfold base; omega) (by omega)
    unfold base at hp ⊢
    omega
  · exact carry_bound words length canonical

#print axioms power_separation
#print axioms high_small
#print axioms carry_bound
#print axioms rank_formula
end R1Z.PV_CB3_GammaBounds
