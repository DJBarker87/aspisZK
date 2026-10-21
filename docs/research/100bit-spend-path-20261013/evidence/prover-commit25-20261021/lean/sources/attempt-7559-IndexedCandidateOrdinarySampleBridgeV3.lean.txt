import AspisR1Post25Sampler.Funs
import IndexedCandidateOuterByteOutputSuccessV5

/-! Candidate-only source bridge for the unchanged ordinary_sample wrapper.
It consumes the actual extracted candidate low_base_p_digits result and actual
extracted decode8 body; it does not claim production equivalence. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerIndexedOrdinaryBridgeV1

open Aeneas Aeneas.Std Result
open AspisR1Post25Sampler
open AspisR1.ExtractedQM31SamplerIndexedOutputSuccessV5
open AspisR1.SourceSamplerByteRank
open AspisR1.SamplerMachineBounds
open AspisR1.SamplerNatModel

/-- The extracted ordinary wrapper returns exactly decode8 of the digits from
its low_base_p_digits call; the same digits have the rank-mod-P^8 model. -/
theorem ordinary_sample_candidate (block : Array U8 32#usize) :
    ∃ outRank : Array U32 8#usize, ∃ digits : Array U32 8#usize,
      ∃ highWord : U32,
        sampler.low_base_p_digits block = ok (digits, highWord) ∧
        sampler.ordinary_sample block = sampler.decode8 digits ∧
        AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge.values digits =
          ordinaryDigits (rank block) ∧
        AspisR1.SamplerAddDigits.digitsValue P (ordinaryDigits (rank block)) =
          rank block % P^8 ∧
        AspisR1.SamplerRepeatedPass.wordValue
          (AspisR1.ExtractedQM31SamplerPassLoop.words outRank).reverse =
          rank block / P^8 := by
  obtain ⟨outRank, digits, highWord, hlow, _hhigh, hdigits, hquotient⟩ :=
    low_base_p_digits_success block
  refine ⟨outRank, digits, highWord, hlow, ?_, hdigits, ?_, hquotient⟩
  · simp only [sampler.ordinary_sample, hlow, bind_tc_ok]
  · rw [AspisR1.SamplerNatModel.ordinaryDigits_value]

#print axioms ordinary_sample_candidate

end AspisR1.ExtractedQM31SamplerIndexedOrdinaryBridgeV1
