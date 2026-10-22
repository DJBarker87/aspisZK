import GammaCallerDigitsModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GammaCaller.DigitsModel
open AspisR1 AspisR1.SamplerNatModel AspisR1.SamplerMachineBounds
open AspisR1.SamplerAddDigits AspisR1.SourceSamplerByteRank

theorem gamma_rank_success (ops : GammaHelpers) (R : HelpersRefine ops)
    (block : Bytes32) (out : field.WideExact)
    (h : sampler.gamma_sample ops block = .ok out) :
    ∃ ds : Digits,
      ops.decode ds = .ok out ∧ Canonical ds ∧
      digitsValue P (values ds) = rank block % (P^8 - 1) + 1 ∧
      0 < digitsValue P (values ds) ∧ digitsValue P (values ds) < P^8 := by
  obtain ⟨ds,hdecode,hdigits⟩ := gamma_digits_success ops R block out h
  have hcanonical : Canonical ds := by
    unfold Canonical
    rw [hdigits]
    exact (gammaDigits_canonical (rank block)).2
  refine ⟨ds,hdecode,hcanonical,?_,?_⟩
  · rw [hdigits]
    exact gammaDigits_value (rank_lt block)
  · rw [hdigits]
    exact gammaDigits_value_bounds (rank_lt block)
#print axioms gamma_rank_success
end AspisR1GammaCaller.DigitsModel
