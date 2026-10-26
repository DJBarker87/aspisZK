import R1LiteralOpeningFunctionalFacts

/-! Prefix projections exposed by a successful common opening-view read.
These are deterministic list facts only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralOpeningPrefixFacts

open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningView

theorem read_prefix_components
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (hread : LiteralOpeningView.read rs = some v) :
    (rs.take 25).length = 25 ∧
    LiteralTranscript.c1At (rs.take 25) = some v.c1 ∧
    LiteralTranscript.c2At (rs.take 25) = some v.c2 ∧
    LiteralSemanticPrefix.read LiteralOpeningView.eK 0 (rs.take 25) = some v.semantic ∧
    v.word = LiteralTypedWords.word ExactBaseProjection.embed
      LiteralOpeningView.eK v.c1 v.c2 := by
  obtain ⟨hc1, hc2, hsemantic, hword⟩ :=
    LiteralOpeningFunctionalFacts.read_semantic_components rs v hread
  have hreadLength := LiteralSemanticPrefix.read_length
    LiteralOpeningView.eK 0 (rs.take 25) v.semantic hsemantic
  have hprefixLength : (rs.take 25).length = 25 := by
    rw [v.semantic_length] at hreadLength
    exact hreadLength.symm
  have htakeDrop : rs.take 25 ++ rs.drop 25 = rs :=
    List.take_append_drop 25 rs
  have htakePositive : 0 < (rs.take 25).length := by omega
  have hc1Append := LiteralTranscript.c1At_append
    (rs.take 25) (rs.drop 25) htakePositive
  have hc1Prefix : LiteralTranscript.c1At (rs.take 25) = some v.c1 := by
    rw [htakeDrop] at hc1Append
    exact hc1Append.symm.trans hc1
  have htakeC2 : 2 < (rs.take 25).length := by omega
  have hc2Append := LiteralTranscript.c2At_append
    (rs.take 25) (rs.drop 25) htakeC2
  have hc2Prefix : LiteralTranscript.c2At (rs.take 25) = some v.c2 := by
    rw [htakeDrop] at hc2Append
    exact hc2Append.symm.trans hc2
  exact ⟨hprefixLength, hc1Prefix, hc2Prefix, hsemantic, hword⟩

#print axioms read_prefix_components

end AspisR1.LiteralOpeningPrefixFacts
end
