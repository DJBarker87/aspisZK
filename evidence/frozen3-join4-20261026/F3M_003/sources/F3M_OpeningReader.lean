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
  · cases c1 : c1At rs <;> simp only [c1,Option.bind_none,Option.bind_some] at read
    next c1v =>
      cases c2 : c2At rs <;> simp only [c2,Option.bind_none,Option.bind_some] at read
      next c2v =>
        cases sem : LiteralSemanticPrefix.read LiteralOpeningView.eK 0 (rs.take 25) with
        | none => simp only [sem] at read; contradiction
        | some semantic =>
          simp only [sem] at read
          cases z0 : LiteralChallengeRead.ordinaryAt rs 25 <;> simp only [z0,Option.bind_none,Option.bind_some] at read
          next z0v =>
            cases z1 : LiteralChallengeRead.ordinaryAt rs 26 <;> simp only [z1,Option.bind_none,Option.bind_some] at read
            next z1v =>
              have same := Option.some.inj read
              subst v
              exact ⟨sem,z0,z1,rfl⟩
  · contradiction

#print axioms components
end AspisR1.F3M_OpeningReader
end
