import T2R_Public
set_option autoImplicit false
noncomputable section
namespace AspisR1.T2R_CarrierGap
open AspisV8R19.DuplexFrames

/-- Carrier-only counterexample to a universal 1880-byte claim. This does not
assert the full remaining runtime/model hypotheses hold for this transcript. -/
theorem arbitrary_public :
    ∃ tr : RawCutTranscriptRun.ErasedPrefix,
      tr.statement.pubBytes = [] ∧ tr.statement.tag = 2 ∧
      tr.statement.pubBytes.length ≠ 1880 := by
  have fit : 75 + ([] : Bytes).length ≤ SelectedTranscriptParams.L := by
    norm_num [SelectedTranscriptParams.L]
  exact ⟨⟨⟨[],fit,2⟩,[]⟩,rfl,rfl,by decide⟩

#print axioms arbitrary_public
end AspisR1.T2R_CarrierGap
end
