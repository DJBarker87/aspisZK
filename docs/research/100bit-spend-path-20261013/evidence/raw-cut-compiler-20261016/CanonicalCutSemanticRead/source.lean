import CanonicalCutEnrichedTranscript
import R1LiteralSemanticPrefix
import R1LiteralOpeningView
import R1LiteralChallengeRead
import R1SelectedChallengeMap

/-! The cut-derived transcript metadata preserves strict-reader success and
the ordinary challenge sequence. Semantic outputs may change where the C2
callback changes; only their successful parsing and challenge projection are
transported here. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.CanonicalCutSemanticRead

open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.LiteralSemanticPrefix
open AspisR1.LiteralTranscript
open AspisR1.LiteralOpeningView

def selectedCirclePoints (z0 z1 : AspisWideTower.WideExact) :
    Fin 2 → AspisR0.ChordGeometry.Point AspisWideTower.WideExact := fun i =>
  if i.val = 0 then
    R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf z0)
  else
    R0P.SemSource.circleSampleParameter1 (SelectedChallengeMap.rhoOf z1)

private def readerCirclePoints (z0 z1 : AspisWideTower.WideExact) :
    Fin 2 → AspisR0.ChordGeometry.Point AspisWideTower.WideExact := fun i =>
  if i = 0 then
    R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf z0)
  else
    R0P.SemSource.circleSampleParameter1 (SelectedChallengeMap.rhoOf z1)

private theorem readerCirclePoints_eq_selected (z0 z1 : AspisWideTower.WideExact) :
    readerCirclePoints z0 z1 = selectedCirclePoints z0 z1 := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [readerCirclePoints, selectedCirclePoints]
  · have hval : i.val ≠ 0 := by
      intro h
      apply hi
      exact Fin.ext h
    simp [readerCirclePoints, selectedCirclePoints, hi, hval]

theorem getElem?_enrichRounds
    (w : Words) (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) :
    (enrichRounds w rs)[i]? =
      (rs[i]?).map fun mc => (enrichMessage w mc.1, mc.2) := by
  induction rs generalizing i with
  | nil => simp [enrichRounds]
  | cons item rest ih =>
      cases i with
      | zero => simp [enrichRounds]
      | succ i => simp [enrichRounds, ih]

theorem c1At_enrichRounds_of_success
    (w : Words) (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (c1 : LiteralTranscript.C1Word)
    (h : LiteralTranscript.c1At rs = some c1) :
    LiteralTranscript.c1At (enrichRounds w rs) = some w.c1 := by
  unfold LiteralTranscript.c1At at h ⊢
  rw [getElem?_enrichRounds]
  cases hget : rs[0]? with
  | none => simp [hget] at h
  | some item =>
      rcases item with ⟨message, challenge⟩
      cases hmessage : message with
      | initial root old => simp [hget, hmessage, enrichMessage] at h ⊢
      | payload bytes => simp [hget, hmessage] at h
      | c2 bytes old => simp [hget, hmessage] at h
      | second bytes old => simp [hget, hmessage] at h

theorem c2At_enrichRounds_of_success
    (w : Words) (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (c2 : LiteralTranscript.C2Word)
    (h : LiteralTranscript.c2At rs = some c2) :
    LiteralTranscript.c2At (enrichRounds w rs) = some w.c2 := by
  unfold LiteralTranscript.c2At at h ⊢
  rw [getElem?_enrichRounds]
  cases hget : rs[2]? with
  | none => simp [hget] at h
  | some item =>
      rcases item with ⟨message, challenge⟩
      cases hmessage : message with
      | initial root old => simp [hget, hmessage] at h
      | payload bytes => simp [hget, hmessage] at h
      | c2 bytes old => simp [hget, hmessage, enrichMessage] at h ⊢
      | second bytes old => simp [hget, hmessage] at h

theorem ordinaryAt_enrichRounds
    (w : Words) (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (i : Nat) :
    LiteralChallengeRead.ordinaryAt (enrichRounds w rs) i =
      LiteralChallengeRead.ordinaryAt rs i := by
  unfold LiteralChallengeRead.ordinaryAt
  rw [getElem?_enrichRounds]
  cases hget : rs[i]? <;> simp [hget]

private theorem valid_initial_word_irrel (i : Nat) (root : State)
    (x y : LiteralTranscript.C1Word) :
    LiteralTranscript.valid i (.initial root x) =
      LiteralTranscript.valid i (.initial root y) := by
  by_cases hi : i = 0
  · subst i
    rfl
  · simp [LiteralTranscript.valid, hi]

private theorem valid_c2_word_irrel (i : Nat) (bytes : LiteralTranscript.BytesMessage)
    (x y : LiteralTranscript.C2Word) :
    LiteralTranscript.valid i (.c2 bytes x) =
      LiteralTranscript.valid i (.c2 bytes y) := by
  by_cases hi : i = 2
  · subst i
    rfl
  · simp [LiteralTranscript.valid, hi]

theorem parseMessage_isSome_enrich
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (row : Fin 25) (w : Words) (m : LiteralTranscript.Message) :
    (LiteralSemanticPrefix.parseMessage eK row (enrichMessage w m)).isSome =
      (LiteralSemanticPrefix.parseMessage eK row m).isSome := by
  cases m with
  | initial root old =>
      have hvEq := valid_initial_word_irrel row.val root w.c1 old
      by_cases hv : LiteralTranscript.valid row.val (.initial root w.c1)
      · have hvOld : LiteralTranscript.valid row.val (.initial root old) := by
          rw [← hvEq]
          exact hv
        simp [LiteralSemanticPrefix.parseMessage, enrichMessage, hv, hvOld]
      · have hvOld : ¬ LiteralTranscript.valid row.val (.initial root old) := by
          intro h
          apply hv
          rw [hvEq]
          exact h
        simp [LiteralSemanticPrefix.parseMessage, enrichMessage, hv, hvOld]
  | payload bytes => rfl
  | c2 bytes old =>
      have hvEq := valid_c2_word_irrel row.val bytes w.c2 old
      by_cases hv : LiteralTranscript.valid row.val (.c2 bytes w.c2)
      · have hvOld : LiteralTranscript.valid row.val (.c2 bytes old) := by
          rw [← hvEq]
          exact hv
        simp [LiteralSemanticPrefix.parseMessage, enrichMessage, hv, hvOld]
      · have hvOld : ¬ LiteralTranscript.valid row.val (.c2 bytes old) := by
          intro h
          apply hv
          rw [hvEq]
          exact h
        simp [LiteralSemanticPrefix.parseMessage, enrichMessage, hv, hvOld]
  | second bytes old => simp [enrichMessage, LiteralSemanticPrefix.parseMessage,
      LiteralTranscript.valid]

theorem read_enriched_success
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (w : Words) (offset : Nat)
    (xs : List (LiteralSemanticPrefix.Message × LiteralSemanticPrefix.Challenge))
    (out : List (R0P.Mask.SemMsgZ LiteralSemanticPrefix.E ×
      LiteralSemanticPrefix.E))
    (h : LiteralSemanticPrefix.read eK offset xs = some out) :
    ∃ out',
      LiteralSemanticPrefix.read eK offset (enrichRounds w xs) = some out' ∧
        out'.map Prod.snd = out.map Prod.snd := by
  induction xs generalizing offset out with
  | nil =>
      simp [LiteralSemanticPrefix.read] at h
      subst out
      exact ⟨[], by simp [LiteralSemanticPrefix.read, enrichRounds], rfl⟩
  | cons item rest ih =>
      rcases item with ⟨message, challenge⟩
      by_cases hoff : offset < 25
      · cases hchallenge : challenge.1 with
        | queries result =>
            simp [LiteralSemanticPrefix.read, hoff, hchallenge] at h
        | ordinary c =>
            cases hparsed : LiteralSemanticPrefix.parseMessage eK
                ⟨offset, hoff⟩ message with
            | none =>
                simp [LiteralSemanticPrefix.read, hoff, hchallenge, hparsed] at h
            | some parsed =>
                cases htail : LiteralSemanticPrefix.read eK (offset + 1) rest with
                | none =>
                    simp [LiteralSemanticPrefix.read, hoff, hchallenge,
                      hparsed, htail] at h
                | some tail =>
                    have hnewParsedExists : ∃ parsed',
                        LiteralSemanticPrefix.parseMessage eK ⟨offset, hoff⟩
                          (enrichMessage w message) = some parsed' := by
                      cases hnewParsed : LiteralSemanticPrefix.parseMessage eK
                          ⟨offset, hoff⟩ (enrichMessage w message) with
                      | none =>
                          have hisSome := parseMessage_isSome_enrich eK
                            ⟨offset, hoff⟩ w message
                          simp [hnewParsed, hparsed] at hisSome
                      | some parsed' => exact ⟨parsed', rfl⟩
                    obtain ⟨parsed', hnewParsed⟩ := hnewParsedExists
                    obtain ⟨tail', hnewTail, hchallengeTail⟩ :=
                      ih (offset + 1) tail htail
                    have hout : (parsed, c) :: tail = out := by
                      simpa [LiteralSemanticPrefix.read, hoff, hchallenge,
                        hparsed, htail] using h
                    cases hout
                    refine ⟨(parsed', c) :: tail', ?_, ?_⟩
                    · simpa [LiteralSemanticPrefix.read, enrichRounds, hoff,
                        hchallenge, hnewParsed, hnewTail]
                    · simp [hchallengeTail]
      · simp [LiteralSemanticPrefix.read, hoff] at h

theorem read_enriched_challenges
    (eK : AspisV8R15.ExactTowerBase.QM31Exact →+* LiteralSemanticPrefix.E)
    (w : Words) (xs : List (LiteralSemanticPrefix.Message × LiteralSemanticPrefix.Challenge))
    (out : List (R0P.Mask.SemMsgZ LiteralSemanticPrefix.E ×
      LiteralSemanticPrefix.E))
    (h : LiteralSemanticPrefix.read eK 0 xs = some out) :
    ∃ out',
      LiteralSemanticPrefix.read eK 0 (enrichRounds w xs) = some out' ∧
        out'.map Prod.snd = out.map Prod.snd :=
  read_enriched_success eK w 0 xs out h

theorem read_all_components
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (hread : LiteralOpeningView.read rs = some v) :
    (rs.take 25).length = 25 ∧
    LiteralTranscript.c1At rs = some v.c1 ∧
    LiteralTranscript.c2At rs = some v.c2 ∧
    LiteralSemanticPrefix.read LiteralOpeningView.eK 0 (rs.take 25) =
      some v.semantic ∧
    LiteralChallengeRead.ordinaryAt rs 25 = some v.challenge25 ∧
    LiteralChallengeRead.ordinaryAt rs 26 = some v.challenge26 ∧
    v.circlePoints = selectedCirclePoints v.challenge25 v.challenge26 ∧
    v.functionals = SelectedOpeningFunctionals.functionals
      (E := AspisWideTower.WideExact) (v.semantic.map Prod.snd)
      (selectedCirclePoints v.challenge25 v.challenge26) ∧
    v.baseFunctional = SelectedOpeningFunctionals.rawBase
      (E := AspisWideTower.WideExact) (v.semantic.map Prod.snd)
      (selectedCirclePoints v.challenge25 v.challenge26) := by
  unfold LiteralOpeningView.read at hread
  split at hread
  · rename_i hprefix'
    cases hc1' : LiteralTranscript.c1At rs with
    | none => simp [hc1'] at hread
    | some c1 =>
      cases hc2' : LiteralTranscript.c2At rs with
      | none => simp [hc1', hc2'] at hread
      | some c2 =>
        simp only [hc1', hc2', Option.bind_some] at hread
        split at hread
        · simp at hread
        · rename_i semantic hsem
          cases hz0 : LiteralChallengeRead.ordinaryAt rs 25 with
          | none => simp [hsem, hz0] at hread
          | some z0 =>
            cases hz1 : LiteralChallengeRead.ordinaryAt rs 26 with
            | none => simp [hsem, hz0, hz1] at hread
            | some z1 =>
              let circlePoints : Fin 2 →
                  AspisR0.ChordGeometry.Point AspisWideTower.WideExact := fun i =>
                if i = 0 then
                  R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf z0)
                else
                  R0P.SemSource.circleSampleParameter1 (SelectedChallengeMap.rhoOf z1)
              let expected : LiteralOpeningView.View :=
                { c1 := c1
                  c2 := c2
                  word := LiteralTypedWords.word ExactBaseProjection.embed
                    LiteralOpeningView.eK c1 c2
                  semantic := semantic
                  semantic_length := by
                    have hlen := LiteralSemanticPrefix.read_length
                      LiteralOpeningView.eK 0 (rs.take 25) semantic hsem
                    rw [hlen]
                    exact hprefix'
                  challenge25 := z0
                  challenge26 := z1
                  circlePoints := circlePoints
                  functionals := SelectedOpeningFunctionals.functionals
                    (E := AspisWideTower.WideExact)
                    (semantic.map Prod.snd) circlePoints
                  baseFunctional := SelectedOpeningFunctionals.rawBase
                    (E := AspisWideTower.WideExact)
                    (semantic.map Prod.snd) circlePoints }
              have hv : expected = v := by
                apply Option.some.inj
                change some expected = some v
                simpa [expected, circlePoints, hsem, hz0, hz1] using hread
              have hpoints : circlePoints = selectedCirclePoints z0 z1 := by
                have hreader : circlePoints = readerCirclePoints z0 z1 := by
                  rfl
                exact hreader.trans (readerCirclePoints_eq_selected z0 z1)
              rw [← hv]
              exact ⟨hprefix', by simpa [expected] using hc1',
                by simpa [expected] using hc2',
                by simpa [expected] using hsem,
                by simpa [expected] using hz0,
                by simpa [expected] using hz1, by
                  change readerCirclePoints z0 z1 = selectedCirclePoints z0 z1
                  exact readerCirclePoints_eq_selected z0 z1,
                by
                  simpa [expected, circlePoints, hpoints],
                by
                  simpa [expected, circlePoints, hpoints]⟩
  · simp at hread

private theorem read_components_construct
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (c1 : LiteralTranscript.C1Word) (c2 : LiteralTranscript.C2Word)
    (semantic : List (R0P.Mask.SemMsgZ AspisWideTower.WideExact ×
      AspisWideTower.WideExact)) (z0 z1 : AspisWideTower.WideExact)
    (hprefix : (rs.take 25).length = 25)
    (hc1 : LiteralTranscript.c1At rs = some c1)
    (hc2 : LiteralTranscript.c2At rs = some c2)
    (hsem : LiteralSemanticPrefix.read LiteralOpeningView.eK 0 (rs.take 25) =
      some semantic)
    (hz0 : LiteralChallengeRead.ordinaryAt rs 25 = some z0)
    (hz1 : LiteralChallengeRead.ordinaryAt rs 26 = some z1) :
    LiteralOpeningView.read rs = some
      { c1 := c1
        c2 := c2
        word := LiteralTypedWords.word ExactBaseProjection.embed
          LiteralOpeningView.eK c1 c2
        semantic := semantic
        semantic_length := by
          have hlen := LiteralSemanticPrefix.read_length LiteralOpeningView.eK
            0 (rs.take 25) semantic hsem
          rw [hlen]
          exact hprefix
        challenge25 := z0
        challenge26 := z1
        circlePoints := selectedCirclePoints z0 z1
        functionals := SelectedOpeningFunctionals.functionals
          (E := AspisWideTower.WideExact) (semantic.map Prod.snd)
          (selectedCirclePoints z0 z1)
        baseFunctional := SelectedOpeningFunctionals.rawBase
          (E := AspisWideTower.WideExact) (semantic.map Prod.snd)
          (selectedCirclePoints z0 z1) } := by
  unfold LiteralOpeningView.read
  simp only [dif_pos hprefix, hc1, Option.bind_some, hc2]
  split
  · simp [hsem] at *
  · rename_i sem hmatched
    have hsemEq : sem = semantic := Option.some.inj (hmatched.symm.trans hsem)
    subst sem
    rw [hz0, hz1]
    rfl

theorem opening_read_enriched_success
    (w : Words)
    (rs : List (LiteralTranscript.Message × LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (hread : LiteralOpeningView.read rs = some v) :
    ∃ v',
      LiteralOpeningView.read (enrichRounds w rs) = some v' ∧
      v'.c1 = w.c1 ∧ v'.c2 = w.c2 ∧
      v'.word = LiteralTypedWords.word ExactBaseProjection.embed LiteralOpeningView.eK w.c1 w.c2 ∧
      v'.challenge25 = v.challenge25 ∧ v'.challenge26 = v.challenge26 ∧
      v'.semantic.map Prod.snd = v.semantic.map Prod.snd ∧
      v'.functionals = v.functionals ∧ v'.baseFunctional = v.baseFunctional := by
  obtain ⟨hprefix, hc1, hc2, hsemantic, hz0, hz1, hcircle, hfuncOld, hbaseOld⟩ :=
    read_all_components rs v hread
  have hprefixEnriched :
      ((enrichRounds w rs).take 25).length = 25 := by
    simpa [enrichRounds] using hprefix
  have hc1Enriched : LiteralTranscript.c1At (enrichRounds w rs) = some w.c1 :=
    c1At_enrichRounds_of_success w rs v.c1 hc1
  have hc2Enriched : LiteralTranscript.c2At (enrichRounds w rs) = some w.c2 :=
    c2At_enrichRounds_of_success w rs v.c2 hc2
  have htake : (enrichRounds w rs).take 25 = enrichRounds w (rs.take 25) := by
    induction rs with
    | nil => rfl
    | cons item rest ih =>
        simp [enrichRounds, ih]
  obtain ⟨semantic', hsemantic', hsemanticChallenges⟩ :=
    read_enriched_success LiteralOpeningView.eK w 0 (rs.take 25) v.semantic hsemantic
  have hsemanticRound :
      LiteralSemanticPrefix.read LiteralOpeningView.eK 0
        ((enrichRounds w rs).take 25) = some semantic' := by
    simpa [htake] using hsemantic'
  have hz0Enriched : LiteralChallengeRead.ordinaryAt (enrichRounds w rs) 25 =
      some v.challenge25 := by
    rw [ordinaryAt_enrichRounds]
    exact hz0
  have hz1Enriched : LiteralChallengeRead.ordinaryAt (enrichRounds w rs) 26 =
      some v.challenge26 := by
    rw [ordinaryAt_enrichRounds]
    exact hz1
  let circlePoints := selectedCirclePoints v.challenge25 v.challenge26
  have hconstructed := read_components_construct (enrichRounds w rs) w.c1 w.c2
    semantic' v.challenge25 v.challenge26 hprefixEnriched hc1Enriched
    hc2Enriched hsemanticRound hz0Enriched hz1Enriched
  let v' : LiteralOpeningView.View :=
    { c1 := w.c1
      c2 := w.c2
      word := LiteralTypedWords.word ExactBaseProjection.embed
        LiteralOpeningView.eK w.c1 w.c2
      semantic := semantic'
      semantic_length := by
        have hlen := LiteralSemanticPrefix.read_length LiteralOpeningView.eK 0
          ((enrichRounds w rs).take 25) semantic' hsemanticRound
        rw [hprefixEnriched] at hlen
        exact hlen
      challenge25 := v.challenge25
      challenge26 := v.challenge26
      circlePoints := circlePoints
      functionals := SelectedOpeningFunctionals.functionals
        (E := AspisWideTower.WideExact) (semantic'.map Prod.snd) circlePoints
      baseFunctional := SelectedOpeningFunctionals.rawBase
        (E := AspisWideTower.WideExact) (semantic'.map Prod.snd) circlePoints }
  have hview : LiteralOpeningView.read (enrichRounds w rs) = some v' := by
    simpa [v', circlePoints, selectedCirclePoints] using hconstructed
  refine ⟨v', hview, rfl, rfl, rfl, rfl, rfl, hsemanticChallenges, ?_, ?_⟩
  · simpa [v', circlePoints, selectedCirclePoints, hsemanticChallenges] using
      hfuncOld.symm
  · simpa [v', circlePoints, selectedCirclePoints, hsemanticChallenges] using
      hbaseOld.symm

#print axioms parseMessage_isSome_enrich
#print axioms read_enriched_success
#print axioms read_enriched_challenges
#print axioms read_all_components
#print axioms opening_read_enriched_success
#print axioms AspisR1.CanonicalCutEnrichedTranscript.wordsFromRawCuts_eq_full

end AspisR1.CanonicalCutSemanticRead
end
