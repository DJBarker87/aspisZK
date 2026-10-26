import R1Z.PV_CB3_GammaBounds
import R1Z.PV_CB3_DigitInjective
namespace R1Z.PV_CB3_GammaExact
open PV_CB3_SamplerCarry PV_CB3_SamplerWord PV_CB3_GammaRank
set_option autoImplicit false

/-- Any canonical eight-digit implementation with the rank formula has exactly
the same digits as the proved recurrence. This is a value-to-array transport
lemma, not a source implementation hypothesis being discharged. -/
theorem unique_digits (words result : List Nat) (word_length : words.length = 8)
    (word_bound : ∀ d, d ∈ words → d < radix)
    (result_length : result.length = 8)
    (result_bound : ∀ d, d ∈ result → d < base)
    (formula : value base result = value radix words % (base ^ 8 - 1) + 1) :
    result = sampleDigits base radix 8 words := by
  apply PV_CB3_DigitInjective.value_injective base (by unfold base; omega)
    result (sampleDigits base radix 8 words)
  · rw [sample_length, result_length]
  · exact result_bound
  · exact sample_canonical base radix 8 (by unfold base; omega) words
  · rw [PV_CB3_GammaBounds.rank_formula words word_length word_bound]
    exact formula

/-- The recurrence produces a nonzero representative within the precise
multiplicative-group cardinality; no large numeral is evaluated. -/
theorem representative_range (words : List Nat) (word_length : words.length = 8)
    (word_bound : ∀ d, d ∈ words → d < radix) :
    0 < value base (sampleDigits base radix 8 words) ∧
      value base (sampleDigits base radix 8 words) ≤ base ^ 8 - 1 := by
  rw [PV_CB3_GammaBounds.rank_formula words word_length word_bound]
  have hp := PV_CB3_GammaBounds.power_separation base 8 (by unfold base; omega) (by omega)
  have hm := Nat.mod_lt (value radix words) (by omega : 0 < base ^ 8 - 1)
  omega

#print axioms unique_digits
#print axioms representative_range
end R1Z.PV_CB3_GammaExact
