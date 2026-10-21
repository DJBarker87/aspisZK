import R4Transport2WideReference

/-! Explicit bounds consumed by the split Kani division/carry checks. -/
set_option autoImplicit false
namespace AspisR1.R4Transport2WideBounds
open Aeneas Aeneas.Std Result
open ExtractedQM31SamplerPassLoop

theorem eight_passes_bounds (block : Array U8 32#usize) (rank : Array U32 8#usize)
    (hbytes : (words rank).reverse = SamplerBytePass.digits block) :
    ∃ ds out, R4Transport2WideReference.extractedRun 8 rank = ok (ds,out) ∧
      (∀ d ∈ ds, d < SamplerMachineBounds.P) ∧
      SamplerRepeatedPass.wordValue (words out).reverse + 1 ≤ 257 := by
  obtain ⟨ds,out,hexec,hds,hout⟩ :=
    R4Transport2WideReference.eight_passes_byte_model block rank hbytes
  refine ⟨ds,out,hexec,?_,?_⟩
  · rw [hds]
    exact SamplerNatModel.lowDigits_canonical SamplerMachineBounds.P_pos 8
      (SourceSamplerByteRank.rank block)
  · rw [hout]
    exact SamplerMachineBounds.rank_quotient_plus_one_le_257 (SourceSamplerByteRank.rank_lt block)

#print axioms eight_passes_bounds
end AspisR1.R4Transport2WideBounds
