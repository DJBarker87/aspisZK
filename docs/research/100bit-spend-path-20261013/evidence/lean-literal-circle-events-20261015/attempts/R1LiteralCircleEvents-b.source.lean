import R1LiteralCircleDensity
import R1LiteralChallengeRead

/-! Bind the row-26 circle event's prior point to the ordinary challenge read
at row 25. This is sampler-density plumbing only; it does not establish that
the prefix arises from an accepted execution or that a terminal event occurs. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralCircleEvents

open FS FS2
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.SourceDuplexStep
attribute [local instance] Classical.propDecidable

/-- At row 26, use the row-25 ordinary challenge as the fixed `z0` input to
`LiteralCircleDensity.bad1`. If row 25 is missing or not ordinary, the event
is false. -/
def bad1 (P : LiteralTranscript.Prefix) (v : AspisWideTower.WideExact) : Prop :=
  match LiteralChallengeRead.ordinaryAt P.rounds 25 with
  | none => False
  | some z =>
      LiteralCircleDensity.bad1
        (R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf z)) v

theorem not_bad0_ne_fallback (z : AspisWideTower.WideExact)
    (h : ¬ LiteralCircleDensity.bad0 z) :
    R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf z) ≠
      R0P.SemSource.circleFallback1 := by
  intro he
  apply h
  unfold LiteralCircleDensity.bad0
  change R0P.SemSource.z0Bad'
    (R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf z))
  unfold R0P.SemSource.z0Bad'
  exact Or.inr he

theorem bad1_mean (P : LiteralTranscript.Prefix) :
    mean (fun s : State =>
      indicator (bad1 P (SelectedChallengeMap.sigma 26 s))) ≤
        LiteralCircleDensity.budget := by
  cases hread : LiteralChallengeRead.ordinaryAt P.rounds 25 with
  | none =>
      have heq :
          (fun s : State => indicator (bad1 P (SelectedChallengeMap.sigma 26 s))) =
            fun _ => (0 : ℚ) := by
        funext s
        simp only [bad1, hread, indicator_false]
      rw [heq, mean_const]
      exact LiteralCircleDensity.budget_nonneg
  | some z =>
      simpa [bad1, hread] using
        LiteralCircleDensity.bad1_mean
          (R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf z))

theorem row26_density
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 26) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator
        (LiteralOrdinaryDensity.event P m (bad1 P) v.2)) ≤
          LiteralCircleDensity.budget := by
  have hi : P.round ≠ 31 := by omega
  have hmass :
      mean (fun s : State =>
        indicator (bad1 P (SelectedChallengeMap.sigma P.round s))) ≤
          LiteralCircleDensity.budget := by
    simpa [hround] using bad1_mean P
  exact LiteralOrdinaryDensity.density P m (bad1 P)
    LiteralCircleDensity.budget hi LiteralCircleDensity.budget_nonneg hmass

#print axioms bad1_mean
#print axioms row26_density
#print axioms not_bad0_ne_fallback

end AspisR1.LiteralCircleEvents
end
