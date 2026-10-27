import F3M_ReaderChallenges
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_OpeningReader
open LiteralTranscript

theorem components (rs : List (Message × Challenge)) (v : LiteralOpeningView.View)
    (read : LiteralOpeningView.read rs=some v) :
    LiteralSemanticPrefix.read LiteralOpeningView.eK 0 (rs.take 25)=some v.semantic ∧
    LiteralChallengeRead.ordinaryAt rs 25=some v.challenge25 ∧
    LiteralChallengeRead.ordinaryAt rs 26=some v.challenge26 ∧
    v.circlePoints=(fun j=>if j.val=0 then
      R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf v.challenge25)
      else R0P.SemSource.circleSampleParameter1 (SelectedChallengeMap.rhoOf v.challenge26)) := by
  unfold LiteralOpeningView.read at read
  split at read
  · rename_i hprefix
    cases hc1 : AspisR1.LiteralTranscript.c1At rs with
    | none => simp [hc1] at read
    | some c1 =>
      cases hc2 : AspisR1.LiteralTranscript.c2At rs with
      | none => simp [hc1, hc2] at read
      | some c2 =>
        simp only [hc1, hc2, Option.bind_some] at read
        split at read
        · simp at read
        · rename_i semantic hsem
          cases hz0 : AspisR1.LiteralChallengeRead.ordinaryAt rs 25 with
          | none => simp [hc1, hc2, hsem, hz0] at read
          | some z0 =>
            cases hz1 : AspisR1.LiteralChallengeRead.ordinaryAt rs 26 with
            | none => simp [hc1, hc2, hsem, hz0, hz1] at read
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
                simpa [expected, circlePoints, hsem, hz0, hz1] using read
              rw [← hv]
              exact ⟨hsem,rfl,rfl,rfl⟩
  · simp at read

#print axioms components
end AspisR1.F3M_OpeningReader
end
