import R1Z.PV_CB3_GammaDigits
import R1Z.PV_CB3_DigitSequence
namespace R1Z.PV_CB3_GammaRank
open PV_CB3_SamplerCarry PV_CB3_DigitSequence PV_CB3_GammaDigits
set_option autoImplicit false

theorem finish_modulus (base : Nat) (positive : 0 < base)
    (digits : List Nat) (high : Nat)
    (canonical : ∀ d, d ∈ digits → d < base)
    (power_large : 2 ≤ base ^ digits.length)
    (high_bound : high < base ^ digits.length - 1) :
    value base (finish base digits high) =
      (value base digits + base ^ digits.length * high) % (base ^ digits.length - 1) + 1 := by
  rw [finish_value base positive digits high canonical high_bound]
  exact PV_CB3_GammaWrap.wrap_increment _ _ _ power_large
    (value_lt_pow base digits canonical) high_bound

/-- Mathematical view of the source's complete digit-and-carry pipeline. -/
def sampleDigits (base radix count : Nat) (words : List Nat) : List Nat :=
  let split := splitDigits base radix count words
  finish base split.1 (value radix split.2)

theorem sample_length (base radix count : Nat) (words : List Nat) :
    (sampleDigits base radix count words).length = count := by
  dsimp only [sampleDigits]
  rw [finish_length, digits_length]

theorem sample_canonical (base radix count : Nat) (positive : 0 < base)
    (words : List Nat) : ∀ d, d ∈ sampleDigits base radix count words → d < base := by
  exact finish_canonical base positive _ _

/-- Closed form derived from the recurrences; all inputs remain arbitrary.
The bound is on the internally computed rank quotient. -/
theorem sample_value (base radix count : Nat) (positive : 0 < base)
    (words : List Nat) (power_large : 2 ≤ base ^ count)
    (high_bound : value radix words / base ^ count < base ^ count - 1) :
    value base (sampleDigits base radix count words) =
      value radix words % (base ^ count - 1) + 1 := by
  have high := quotient_value base radix positive count words
  have bound : value radix (splitDigits base radix count words).2 <
      base ^ (splitDigits base radix count words).1.length - 1 := by
    rw [digits_length, ← high]
    exact high_bound
  dsimp only [sampleDigits]
  rw [finish_modulus base positive _ _
    (digits_canonical base radix positive count words)
    (by simpa only [digits_length] using power_large) bound]
  rw [digits_length, value_conserved]

#print axioms finish_modulus
#print axioms sample_length
#print axioms sample_canonical
#print axioms sample_value
end R1Z.PV_CB3_GammaRank
