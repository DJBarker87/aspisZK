import CanonicalCutSemanticRead
import R1CanonicalCutTypedProjection

/-! Composition of the strict opening reader with the existing pointwise
projection of commitment-map decodes. This does not identify source bytes or
claim accepted-verifier correspondence; callers supply the concrete map-word
identity and successful codec decodes. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.CanonicalCutOpeningWordProjection

open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.CanonicalCutSemanticRead
open AspisR1.CanonicalCutTypedProjection
open AspisR1.LiteralOpeningView
open AspisR1.TypedRecoveredWords
open AspisR1.FoldedLeafCodec
open AspisR1.FoldedRecoveredWord
open AspisR1.MerkleIndexGeometry

/-- A successful literal opening read, enriched with commitment-time words,
retains the semantic challenges and has pointwise word values given by the
supplied successful C1/C2/folded packed-map decodes. The `words_eq_maps`
input is intended to be discharged by `RawCutWordsFromView.buildWords_eq_full`
for the actual transcript's raw-byte cut maps. -/
theorem opening_read_enriched_projects_cut_maps
    (w : Words)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (c1Packed c2Packed : Fin 262144 → Option (List ExactLeafFieldCodec.Byte))
    (foldedPacked : Fin 65536 → Option (List ExactLeafFieldCodec.Byte))
    (q : Fin 262144)
    (c1 : TypedRecoveredWords.C1) (c2 : TypedRecoveredWords.C2)
    (folded : FoldedLeafCodec.Folded)
    (hread : LiteralOpeningView.read rs = some v)
    (hwords : w = wordsFromMaps c1Packed c2Packed foldedPacked)
    (hc1 : TypedRecoveredWords.decodeC1At c1Packed
      (queryLeaf (queryPosition q)) = some c1)
    (hc2 : TypedRecoveredWords.decodeC2At c2Packed
      (queryLeaf (queryPosition q)) = some c2)
    (hfolded : (foldedPacked (foldedIndex q)).bind
      FoldedLeafCodec.decodeFolded = some folded) :
    ∃ v',
      LiteralOpeningView.read (enrichRounds w rs) = some v' ∧
      v'.semantic.map Prod.snd = v.semantic.map Prod.snd ∧
      (∀ l : Fin 26,
        v'.word ⟨l.val, by have hl := l.isLt; omega⟩ (queryPosition q) =
          ExactBaseProjection.embed ((c1 (querySlot (queryPosition q))).1 l)) ∧
      v'.word ⟨26, by decide⟩ (queryPosition q) =
        LiteralOpeningView.eK ((c2 (querySlot (queryPosition q))) ⟨0, by decide⟩) ∧
      v'.word ⟨27, by decide⟩ (queryPosition q) =
        LiteralOpeningView.eK ((c2 (querySlot (queryPosition q))) ⟨1, by decide⟩) ∧
      v'.word ⟨28, by decide⟩ (queryPosition q) =
        LiteralOpeningView.eK ((c1 (querySlot (queryPosition q))).2) ∧
      w.final q = folded (foldedSlot q) := by
  obtain ⟨v', hnew, hc1w, hc2w, hword, hz0, hz1, hsem, hfunc, hbase⟩ :=
    opening_read_enriched_success w rs v hread
  have hwc1 : w.c1 = TypedRecoveredWords.c1Value c1Packed := by
    exact congrArg Words.c1 hwords
  have hwc2 : w.c2 = TypedRecoveredWords.c2Value c2Packed := by
    exact congrArg Words.c2 hwords
  have hwfinal : w.final = fun q =>
      FoldedRecoveredWord.wordOfPacked (foldedPacked (foldedIndex q)) q := by
    exact congrArg Words.final hwords
  have hproject := literal_word_from_cut_payloads_at
    (E := AspisWideTower.WideExact) ExactBaseProjection.embed
    LiteralOpeningView.eK c1Packed c2Packed foldedPacked q c1 c2 folded hc1 hc2 hfolded
  rcases hproject with ⟨hbaseLanes, h26, h27, h28, hfoldedWord⟩
  refine ⟨v', hnew, hsem, ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    calc
      v'.word ⟨l.val, by have hl := l.isLt; omega⟩ (queryPosition q) =
          LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
            w.c1 w.c2 ⟨l.val, by have hl := l.isLt; omega⟩ (queryPosition q) := by
              rw [hword]
      _ = LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
            (TypedRecoveredWords.c1Value c1Packed)
            (TypedRecoveredWords.c2Value c2Packed)
            ⟨l.val, by have hl := l.isLt; omega⟩ (queryPosition q) := by
              rw [hwc1, hwc2]
      _ = ExactBaseProjection.embed ((c1 (querySlot (queryPosition q))).1 l) :=
            hbaseLanes l
  · calc
      v'.word ⟨26, by decide⟩ (queryPosition q) =
          LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
            w.c1 w.c2 ⟨26, by decide⟩ (queryPosition q) := by rw [hword]
      _ = LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
            (TypedRecoveredWords.c1Value c1Packed)
            (TypedRecoveredWords.c2Value c2Packed) ⟨26, by decide⟩ (queryPosition q) := by
              rw [hwc1, hwc2]
      _ = LiteralOpeningView.eK ((c2 (querySlot (queryPosition q))) ⟨0, by decide⟩) := h26
  · calc
      v'.word ⟨27, by decide⟩ (queryPosition q) =
          LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
            w.c1 w.c2 ⟨27, by decide⟩ (queryPosition q) := by rw [hword]
      _ = LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
            (TypedRecoveredWords.c1Value c1Packed)
            (TypedRecoveredWords.c2Value c2Packed) ⟨27, by decide⟩ (queryPosition q) := by
              rw [hwc1, hwc2]
      _ = LiteralOpeningView.eK ((c2 (querySlot (queryPosition q))) ⟨1, by decide⟩) := h27
  · calc
      v'.word ⟨28, by decide⟩ (queryPosition q) =
          LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
            w.c1 w.c2 ⟨28, by decide⟩ (queryPosition q) := by rw [hword]
      _ = LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK
            (TypedRecoveredWords.c1Value c1Packed)
            (TypedRecoveredWords.c2Value c2Packed) ⟨28, by decide⟩ (queryPosition q) := by
              rw [hwc1, hwc2]
      _ = LiteralOpeningView.eK ((c1 (querySlot (queryPosition q))).2) := h28
  · rw [hwfinal]
    exact hfoldedWord

#print axioms opening_read_enriched_projects_cut_maps

end AspisR1.CanonicalCutOpeningWordProjection
end
