import FJo_PackedLeaves
import FJo_AdaptedDots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_PackedDecodes
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
/-- Strict decodes transfer to both literal maps using DERIVED sampler uniqueness. -/
theorem value (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (read : queries tr=some q) (j : Fin 22)
    (c1 : MixedLeafEncoding.C1) (c2 : MixedLeafEncoding.C2)
    (d1 : MixedLeafDecoder.decodeC1 ((opening parsed j.val).take 480)=some c1)
    (d2 : MixedLeafDecoder.decodeC2 (slice (opening parsed j.val) 480 128)=some c2) :
    TypedRecoveredWords.decodeC1At (fun i=>packed parsed q 0 i.val) (q j)=some c1 ∧
    TypedRecoveredWords.decodeC2At (fun i=>packed parsed q 1 i.val) (q j)=some c2 := by
  obtain ⟨h1,h2⟩ := FJo_PackedLeaves.value parsed q tr read j
  simp only [TypedRecoveredWords.decodeC1At,TypedRecoveredWords.decodeC2At,h1,h2,Option.bind_eq_bind,Option.bind_some,d1,d2]
  exact ⟨True.intro,True.intro⟩
#print axioms value
end AspisR1.FJo_PackedDecodes
end
