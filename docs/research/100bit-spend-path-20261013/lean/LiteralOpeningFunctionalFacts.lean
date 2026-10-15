import R1LiteralOpeningView

/-! Successful literal opening reads expose the functional values assembled
by the reader. This is a model-level projection fact only. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralOpeningFunctionalFacts

open AspisR1.LiteralOpeningView
open AspisR1.SelectedOpeningFunctionals

attribute [local irreducible] SelectedOpeningFunctionals.functionals
  SelectedOpeningFunctionals.rawBase SelectedOpeningFunctionals.rows
  LiteralTypedWords.word

theorem read_functionals
    (rs : List (AspisR1.LiteralTranscript.Message × AspisR1.LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (hread : LiteralOpeningView.read rs = some v) :
    v.functionals =
        SelectedOpeningFunctionals.functionals (E := AspisWideTower.WideExact)
          (v.semantic.map Prod.snd) v.circlePoints ∧
    v.baseFunctional =
        SelectedOpeningFunctionals.rawBase (E := AspisWideTower.WideExact)
          (v.semantic.map Prod.snd) v.circlePoints := by
  unfold LiteralOpeningView.read at hread
  split at hread
  · rename_i hprefix
    cases hc1 : AspisR1.LiteralTranscript.c1At rs with
    | none => simp [hc1] at hread
    | some c1 =>
      cases hc2 : AspisR1.LiteralTranscript.c2At rs with
      | none => simp [hc1, hc2] at hread
      | some c2 =>
        simp only [hc1, hc2, Option.bind_some] at hread
        split at hread
        · simp at hread
        · rename_i semantic hsem
          cases hz0 : AspisR1.LiteralChallengeRead.ordinaryAt rs 25 with
          | none => simp [hc1, hc2, hsem, hz0] at hread
          | some z0 =>
            cases hz1 : AspisR1.LiteralChallengeRead.ordinaryAt rs 26 with
            | none => simp [hc1, hc2, hsem, hz0, hz1] at hread
            | some z1 =>
              let circlePoints : Fin 2 →
                  AspisR0.ChordGeometry.Point AspisWideTower.WideExact := fun i =>
                if i.val = 0 then
                  R0P.SemSource.circleSampleParameter0
                    (AspisR1.SelectedChallengeMap.rhoOf z0)
                else
                  R0P.SemSource.circleSampleParameter1
                    (AspisR1.SelectedChallengeMap.rhoOf z1)
              let expected : LiteralOpeningView.View :=
                { c1 := c1
                  c2 := c2
                  word := AspisR1.LiteralTypedWords.word
                    AspisR1.ExactBaseProjection.embed
                    AspisR1.LiteralOpeningView.eK c1 c2
                  semantic := semantic
                  semantic_length := by
                    have hlen := AspisR1.LiteralSemanticPrefix.read_length
                      AspisR1.LiteralOpeningView.eK 0 (rs.take 25) semantic hsem
                    rw [hlen]
                    exact hprefix
                  challenge25 := z0
                  challenge26 := z1
                  circlePoints := circlePoints
                  functionals := SelectedOpeningFunctionals.functionals (E := AspisWideTower.WideExact)
                    (semantic.map Prod.snd) circlePoints
                  baseFunctional := SelectedOpeningFunctionals.rawBase (E := AspisWideTower.WideExact)
                    (semantic.map Prod.snd) circlePoints }
              have hv : expected = v := by
                apply Option.some.inj
                change some expected = some v
                simpa [expected, circlePoints, hsem, hz0, hz1] using hread
              rw [← hv]
              exact ⟨rfl, rfl⟩
  · simp at hread

theorem read_semantic_components
    (rs : List (AspisR1.LiteralTranscript.Message × AspisR1.LiteralTranscript.Challenge))
    (v : LiteralOpeningView.View)
    (hread : LiteralOpeningView.read rs = some v) :
    AspisR1.LiteralTranscript.c1At rs = some v.c1 ∧
    AspisR1.LiteralTranscript.c2At rs = some v.c2 ∧
    AspisR1.LiteralSemanticPrefix.read
      LiteralOpeningView.eK 0 (rs.take 25) = some v.semantic ∧
    v.word = AspisR1.LiteralTypedWords.word
      AspisR1.ExactBaseProjection.embed LiteralOpeningView.eK v.c1 v.c2 := by
  unfold LiteralOpeningView.read at hread
  split at hread
  · rename_i hprefix
    cases hc1 : AspisR1.LiteralTranscript.c1At rs with
    | none => simp [hc1] at hread
    | some c1 =>
      cases hc2 : AspisR1.LiteralTranscript.c2At rs with
      | none => simp [hc1, hc2] at hread
      | some c2 =>
        simp only [hc1, hc2, Option.bind_some] at hread
        split at hread
        · simp at hread
        · rename_i semantic hsem
          cases hz0 : AspisR1.LiteralChallengeRead.ordinaryAt rs 25 with
          | none => simp [hc1, hc2, hsem, hz0] at hread
          | some z0 =>
            cases hz1 : AspisR1.LiteralChallengeRead.ordinaryAt rs 26 with
            | none => simp [hc1, hc2, hsem, hz0, hz1] at hread
            | some z1 =>
              let circlePoints : Fin 2 →
                  AspisR0.ChordGeometry.Point AspisWideTower.WideExact := fun i =>
                if i.val = 0 then
                  R0P.SemSource.circleSampleParameter0
                    (AspisR1.SelectedChallengeMap.rhoOf z0)
                else
                  R0P.SemSource.circleSampleParameter1
                    (AspisR1.SelectedChallengeMap.rhoOf z1)
              let expected : LiteralOpeningView.View :=
                { c1 := c1
                  c2 := c2
                  word := AspisR1.LiteralTypedWords.word
                    AspisR1.ExactBaseProjection.embed
                    LiteralOpeningView.eK c1 c2
                  semantic := semantic
                  semantic_length := by
                    have hlen := AspisR1.LiteralSemanticPrefix.read_length
                      LiteralOpeningView.eK 0 (rs.take 25) semantic hsem
                    rw [hlen]
                    exact hprefix
                  challenge25 := z0
                  challenge26 := z1
                  circlePoints := circlePoints
                  functionals := SelectedOpeningFunctionals.functionals (E := AspisWideTower.WideExact)
                    (semantic.map Prod.snd) circlePoints
                  baseFunctional := SelectedOpeningFunctionals.rawBase (E := AspisWideTower.WideExact)
                    (semantic.map Prod.snd) circlePoints }
              have hv : expected = v := by
                apply Option.some.inj
                change some expected = some v
                simpa [expected, circlePoints, hsem, hz0, hz1] using hread
              rw [← hv]
              exact ⟨rfl, rfl, hsem, rfl⟩
  · simp at hread

#print axioms read_functionals
#print axioms read_semantic_components

end AspisR1.LiteralOpeningFunctionalFacts
end
