import CanonicalCutSemanticRead
import RawCutWordsFromRunExecutable

/-! A successful opening parse of a metadata-enriched transcript identifies
the typed word from the enriched round entries themselves. No successful read
of the unenriched transcript is required. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.RawEnrichedOpeningWordIdentity

open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.CanonicalCutSemanticRead
open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningView
open AspisR1.RawCutWordsFromRunExecutable

private theorem c1_enriched_success_identifies
    (w : CanonicalCutEnrichedTranscript.Words)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (c1 : LiteralTranscript.C1Word)
    (h : LiteralTranscript.c1At (enrichRounds w rs) = some c1) :
    c1 = w.c1 := by
  unfold LiteralTranscript.c1At at h
  rw [CanonicalCutSemanticRead.getElem?_enrichRounds] at h
  cases hget : rs[0]? with
  | none => simp [hget] at h
  | some item =>
      rcases item with ⟨message, challenge⟩
      cases hmessage : message with
      | initial root old =>
          simp [hget, hmessage, CanonicalCutEnrichedTranscript.enrichMessage] at h
          exact h.symm
      | payload bytes =>
          simp [hget, hmessage, CanonicalCutEnrichedTranscript.enrichMessage] at h
      | c2 bytes old =>
          simp [hget, hmessage, CanonicalCutEnrichedTranscript.enrichMessage] at h
      | second bytes old =>
          simp [hget, hmessage, CanonicalCutEnrichedTranscript.enrichMessage] at h

private theorem c2_enriched_success_identifies
    (w : CanonicalCutEnrichedTranscript.Words)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (c2 : LiteralTranscript.C2Word)
    (h : LiteralTranscript.c2At (enrichRounds w rs) = some c2) :
    c2 = w.c2 := by
  unfold LiteralTranscript.c2At at h
  rw [CanonicalCutSemanticRead.getElem?_enrichRounds] at h
  cases hget : rs[2]? with
  | none => simp [hget] at h
  | some item =>
      rcases item with ⟨message, challenge⟩
      cases hmessage : message with
      | initial root old =>
          simp [hget, hmessage, CanonicalCutEnrichedTranscript.enrichMessage] at h
      | payload bytes =>
          simp [hget, hmessage, CanonicalCutEnrichedTranscript.enrichMessage] at h
      | c2 bytes old =>
          simp [hget, hmessage, CanonicalCutEnrichedTranscript.enrichMessage] at h
          exact h.symm
      | second bytes old =>
          simp [hget, hmessage, CanonicalCutEnrichedTranscript.enrichMessage] at h

theorem enriched_read_word_eq_fields
    (w : CanonicalCutEnrichedTranscript.Words)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (hread : LiteralOpeningView.read (enrichRounds w rs) = some v) :
    v.c1 = w.c1 ∧ v.c2 = w.c2 ∧
      v.word = LiteralTypedWords.word ExactBaseProjection.embed
        LiteralOpeningView.eK w.c1 w.c2 := by
  obtain ⟨hprefix, hc1, hc2, hsemantic, hz0, hz1, _, _, _⟩ :=
    CanonicalCutSemanticRead.read_all_components (enrichRounds w rs) v hread
  have hc1' : v.c1 = w.c1 := c1_enriched_success_identifies w rs v.c1 hc1
  have hc2' : v.c2 = w.c2 := c2_enriched_success_identifies w rs v.c2 hc2
  let expected : LiteralOpeningView.View :=
    { c1 := v.c1
      c2 := v.c2
      word := LiteralTypedWords.word ExactBaseProjection.embed
        LiteralOpeningView.eK v.c1 v.c2
      semantic := v.semantic
      semantic_length := by
        have hlen := LiteralSemanticPrefix.read_length LiteralOpeningView.eK
          0 ((enrichRounds w rs).take 25) v.semantic hsemantic
        rw [hlen]
        exact hprefix
      challenge25 := v.challenge25
      challenge26 := v.challenge26
      circlePoints := selectedCirclePoints v.challenge25 v.challenge26
      functionals := SelectedOpeningFunctionals.functionals
        (E := AspisWideTower.WideExact) (v.semantic.map Prod.snd)
        (selectedCirclePoints v.challenge25 v.challenge26)
      baseFunctional := SelectedOpeningFunctionals.rawBase
        (E := AspisWideTower.WideExact) (v.semantic.map Prod.snd)
        (selectedCirclePoints v.challenge25 v.challenge26) }
  have hconstruct : LiteralOpeningView.read (enrichRounds w rs) = some expected := by
    unfold LiteralOpeningView.read
    simp only [dif_pos hprefix, hc1, hc2, Option.bind_some]
    split
    · simp [hsemantic] at *
    · rename_i semantic hmatched
      have hsemEq : semantic = v.semantic :=
        Option.some.inj (hmatched.symm.trans hsemantic)
      subst semantic
      rw [hz0, hz1]
      rfl
  have hv : expected = v := Option.some.inj (hconstruct.symm.trans hread)
  have hword : v.word = LiteralTypedWords.word ExactBaseProjection.embed
      LiteralOpeningView.eK v.c1 v.c2 := by
    have hprojected := congrArg LiteralOpeningView.View.word hv
    simpa [expected] using hprojected.symm
  refine ⟨hc1', hc2', ?_⟩
  rw [hword, hc1', hc2']

theorem enriched_read_wordsFromRun_identity
    (run : RawCutProverCompiler.RunView)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (hread : LiteralOpeningView.read (enrichRounds (wordsFromRun run) rs) = some v) :
    v.word = initialWordsFromRun run := by
  obtain ⟨_, _, hword⟩ := enriched_read_word_eq_fields (wordsFromRun run) rs v hread
  simpa [initialWordsFromRun, LiteralOpeningView.eK] using hword

#print axioms enriched_read_word_eq_fields
#print axioms enriched_read_wordsFromRun_identity

end AspisR1.RawEnrichedOpeningWordIdentity
end
