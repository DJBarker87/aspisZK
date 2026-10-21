import IndexedCandidateOuterByteBridgeV13

/-! Candidate-only consumer: turn the exact generated index call in the outer
bridge into an explicit successful return using the standard array-index
specification. No production equivalence is claimed. -/
set_option autoImplicit false

namespace AspisR1.ExtractedQM31SamplerIndexedOutputSuccessV5
open Aeneas Aeneas.Std Result WP
open AspisR1Post25Sampler
open AspisR1.ExtractedQM31SamplerIndexedOuterBridgeV13
open AspisR1.ExtractedQM31SamplerIndexedGeneratedBridge
open AspisR1.ExtractedQM31SamplerIndexedCandidate
open AspisR1.SourceSamplerByteRank
open AspisR1.SamplerMachineBounds
open AspisR1.SamplerRepeatedPass
open AspisR1.SamplerWordPass
open AspisR1.ExtractedQM31SamplerPassLoop
open AspisR1.ExtractedQM31SamplerIndexedCandidate
open AspisR1.SourceSamplerByteRank
open AspisR1.SamplerMachineBounds
open AspisR1.SamplerRepeatedPass
open AspisR1.SamplerWordPass
open AspisR1.ExtractedQM31SamplerPassLoop

private theorem index_zero_success (rank : Array U32 8#usize) :
    ∃ highWord : U32,
      Array.index_usize rank 0#usize = ok highWord ∧
      highWord = rank.val[(0#usize).val] := by
  have hi : (0#usize).val < 8 := by decide
  have hb : (0#usize).val < rank.length := by
    have hr := rank.property
    change rank.val.length = 8 at hr
    change (0#usize).val < rank.val.length
    omega
  obtain ⟨highWord, hindex, hval⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec rank 0#usize hb)
  exact ⟨highWord, hindex, hval⟩

theorem low_base_p_digits_success (block : Array U8 32#usize) :
    ∃ outRank : Array U32 8#usize, ∃ outDigits : Array U32 8#usize, ∃ highWord : U32,
      sampler.low_base_p_digits block = ok (outDigits, highWord) ∧
      highWord = outRank.val[(0#usize).val] ∧
      values outDigits = SamplerNatModel.ordinaryDigits (rank block) ∧
      wordValue ((words outRank).reverse) = rank block / P^8 := by
  obtain ⟨outRank, outDigits, hrun, hdigits, hremaining⟩ :=
    low_base_p_digits_candidate block
  obtain ⟨highWord, hindex, hvalue⟩ := index_zero_success outRank
  have hindexMethod : outRank.index_usize 0#usize = ok highWord := by
    simpa only [Array.index_usize] using hindex
  refine ⟨outRank, outDigits, highWord, ?_, hvalue, hdigits, hremaining⟩
  rw [hrun]
  simp only [hindexMethod, bind_tc_ok]

#print axioms index_zero_success
#print axioms low_base_p_digits_success

end AspisR1.ExtractedQM31SamplerIndexedOutputSuccessV5
