import R1LiteralOrdinaryDensity
import R1SelectedChallengeMap
import R0P.CircleSampler

/-! Fixed-row sampling adapters for the two literal circle challenges. The
second-row bound takes its prior `z0` explicitly; this module does not show
that an execution prefix supplies that value or that a prior no-hit condition
holds. These are density statements only, with no terminal, acceptance, or
Rust-source conclusion. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralCircleDensity

open FS FS2
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw
attribute [local instance] Classical.propDecidable
open AspisV8R19.SourceDuplexStep
open AspisWideTower
open R0P.SemSource

abbrev E := AspisWideTower.WideExact

/-- The old one-fiber circle mass bound, in the current notation. -/
def budget : ℚ :=
  (1 + R0P.SemSource.deltaQ) / (AspisV8R15.ExactTowerBase.P : ℚ)^4

/-- Row-25 bad event applied to an ordinary challenge value. -/
def bad0 (v : E) : Prop :=
  R0P.SemSource.z0Bad'
    (R0P.SemSource.circleSampleParameter0 (SelectedChallengeMap.rhoOf v))

attribute [local irreducible] R0P.SemSource.circleFallback1

/-- Row-26 bad event with its previous point fixed explicitly. -/
def bad1 (z0 : AspisR0.ChordGeometry.Point AspisWideTower.WideExact) (v : E) : Prop :=
  z0 ≠ R0P.SemSource.circleFallback1 ∧
    R0P.SemSource.circleBad1Pred z0 (SelectedChallengeMap.rhoOf v)

theorem budget_nonneg : 0 ≤ budget := by
  unfold budget
  have hdelta := R0P.SemSource.deltaQ_nonneg
  positivity

theorem bad0_mean :
    mean (fun s : State => indicator (bad0 (SelectedChallengeMap.sigma 25 s))) ≤
      budget := by
  have hview (s : State) :
      bad0 (SelectedChallengeMap.sigma 25 s) ↔
        R0P.SemSource.z0Bad' (R0P.SemSource.circleSample0 s) := by
    unfold bad0
    rw [SelectedChallengeMap.first_circle_view]
  rw [mean_congr (fun s => indicator_iff (hview s))]
  simpa [budget] using R0P.SemSource.circleSample0_mass

theorem bad1_mean (z0 : AspisR0.ChordGeometry.Point AspisWideTower.WideExact) :
    mean (fun s : State => indicator (bad1 z0 (SelectedChallengeMap.sigma 26 s))) ≤
      budget := by
  by_cases hz0 : z0 = R0P.SemSource.circleFallback1
  · have hfalse (s : State) : bad1 z0 (SelectedChallengeMap.sigma 26 s) ↔ False := by
      simp [bad1, hz0]
    rw [mean_congr (fun s => indicator_iff (hfalse s))]
    simp only [indicator_false, mean_const]
    exact budget_nonneg
  · have hview (s : State) :
      bad1 z0 (SelectedChallengeMap.sigma 26 s) ↔
        R0C.SemStatement.z1Bad (K := AspisWideTower.WideExact) z0 (R0P.SemSource.circleSample1 s) := by
      unfold bad1 R0P.SemSource.circleBad1Pred
      rw [SelectedChallengeMap.second_circle_view]
      simp [hz0]
    rw [mean_congr (fun s => indicator_iff (hview s))]
    simpa [budget] using R0P.SemSource.circleSample1_mass z0 hz0

theorem row25_density
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 25) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m bad0 v.2)) ≤ budget := by
  have hi : P.round ≠ 31 := by omega
  have hmass :
      mean (fun s : State =>
        indicator (bad0 (SelectedChallengeMap.sigma P.round s))) ≤ budget := by
    simpa [hround] using bad0_mean
  exact LiteralOrdinaryDensity.density P m bad0 budget hi budget_nonneg hmass

theorem row26_density
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (z0 : AspisR0.ChordGeometry.Point AspisWideTower.WideExact) (hround : P.round = 26) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m (bad1 z0) v.2)) ≤ budget := by
  have hi : P.round ≠ 31 := by omega
  have hmass :
      mean (fun s : State =>
        indicator ((bad1 z0) (SelectedChallengeMap.sigma P.round s))) ≤ budget := by
    simpa [hround] using bad1_mean z0
  exact LiteralOrdinaryDensity.density P m (bad1 z0) budget hi budget_nonneg hmass

#print axioms budget_nonneg
#print axioms bad0_mean
#print axioms bad1_mean
#print axioms row25_density
#print axioms row26_density

end AspisR1.LiteralCircleDensity
end
