import GammaCandidateLowQuotient
import GammaCandidateDecodedFieldRank
import GammaCandidateAddSmallHelpersRefine
import NPH_R22FieldRef

/-! NPH_ (R22, item 3 of the 2026-11-10 continuation: the gamma_sample producer bound). Lemmas about
the existing gate definitions; nothing merged changes.

AspisR1GammaCaller.sampler.gamma_sample's only checked operation is quotient + 1 on u32, where
(digits, quotient) is the result of ops.low. Both helper records of the closure install
ops.low = AspisR1Post25Sampler.sampler.low_base_p_digits (`helpers_low`, rfl), and on that producer
the quotient is rank block / P^8 ≤ 256 (AspisR1GammaCaller.DigitsModel.low_candidate_refines and
AspisR1.SamplerMachineBounds.rank_div_P8_le_256 with rank_lt), so quotient + 1 is ok
(`gamma_increment_ok`). Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22Gamma
open Aeneas Aeneas.Std Result AspisR1.NPH_R22FieldRef

theorem gamma_increment_ok (block : Array U8 32#usize) (ds : Array U32 8#usize) (q : U32)
    (h : AspisR1Post25Sampler.sampler.low_base_p_digits block = ok (ds, q)) :
    ∃ n, (q + 1#u32 : Result U32) = ok n ∧ n.val = q.val + 1 := by
  obtain ⟨_, hq⟩ := AspisR1GammaCaller.DigitsModel.low_candidate_refines block ds q h
  have hb := AspisR1.SamplerMachineBounds.rank_div_P8_le_256 (AspisR1.SourceSamplerByteRank.rank_lt block)
  have hq256 : q.val ≤ 256 := by rw [hq]; exact hb
  have h1 : (1#u32 : U32).val = 1 := by first | rfl | simp
  obtain ⟨n, hn, hv⟩ := add_ok q (1#u32) (by rw [h1, max32]; omega)
  exact ⟨n, hn, by rw [hv, h1]⟩

theorem helpers_low (decode : AspisR1GammaCaller.DigitsModel.CandidateDigits →
      Result AspisR1GammaCaller.field.WideExact) :
    (AspisR1GammaCaller.DigitsModel.candidateHelpers decode).low =
        (fun block => AspisR1Post25Sampler.sampler.low_base_p_digits block) ∧
      AspisR1GammaCaller.DigitsModel.candidateGammaHelpers.low =
        (fun block => AspisR1Post25Sampler.sampler.low_base_p_digits block) :=
  ⟨rfl, rfl⟩

#print axioms gamma_increment_ok
#print axioms helpers_low
end AspisR1.NPH_R22Gamma
