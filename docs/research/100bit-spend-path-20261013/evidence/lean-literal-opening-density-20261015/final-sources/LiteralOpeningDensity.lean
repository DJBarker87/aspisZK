import R1LiteralOpeningEvents
import R1LiteralOrdinaryDensity

/-! Independent-answer density bounds for the four opening rows of the literal
protocol. Each input reader is a function of the completed prefix and current
message, fixed before the fresh challenge. These statements do not establish
terminal extraction, source refinement, or the shared-oracle reduction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralOpeningDensity

open FS FS2
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.SourceDuplexStep
open AspisR1.LiteralOpeningEvents
attribute [local instance] Classical.propDecidable

def gammaBudget : ℚ := (336869026622539 : ℚ) * OpeningSamplerBound.gammaAtom
def kappaBudget : ℚ := (600 : ℚ) * OpeningSamplerBound.atom
def foldBudget : ℚ := (9396508281846 : ℚ) * OpeningSamplerBound.atom

theorem gammaBudget_nonneg : 0 ≤ gammaBudget := by
  unfold gammaBudget OpeningSamplerBound.gammaAtom
  positivity

theorem kappaBudget_nonneg : 0 ≤ kappaBudget := by
  unfold kappaBudget OpeningSamplerBound.atom
  positivity

theorem foldBudget_nonneg : 0 ≤ foldBudget := by
  unfold foldBudget OpeningSamplerBound.atom
  positivity

theorem gamma_mean (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    mean (fun s : State => indicator (gammaBad P m (SelectedChallengeMap.sigma 27 s))) ≤
      gammaBudget := by
  cases h : readGamma P m with
  | none =>
      simp only [gammaBad, h, indicator_false, mean_const]
      exact gammaBudget_nonneg
  | some v =>
      simpa only [gammaBad, h, gammaBudget] using
        SelectedOpeningEventMass.gamma_mass v.context.word v.context.functionals v.payload

theorem row27_density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 27) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m (gammaBad P m) v.2)) ≤
      gammaBudget := by
  apply LiteralOrdinaryDensity.density P m (gammaBad P m) gammaBudget
  · omega
  · exact gammaBudget_nonneg
  · simpa only [hround] using gamma_mean P m

theorem kappa_mean (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    mean (fun s : State => indicator (kappaBad P m (SelectedChallengeMap.sigma 28 s))) ≤
      kappaBudget := by
  cases h : readKappa P m with
  | none =>
      simp only [kappaBad, h, indicator_false, mean_const]
      exact kappaBudget_nonneg
  | some v =>
      simpa only [kappaBad, h, kappaBudget] using
        SelectedOpeningEventMass.kappa_mass v.context.word v.context.functionals v.context.baseFunctional v.payload28 v.gamma

theorem row28_density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 28) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m (kappaBad P m) v.2)) ≤
      kappaBudget := by
  apply LiteralOrdinaryDensity.density P m (kappaBad P m) kappaBudget
  · omega
  · exact kappaBudget_nonneg
  · simpa only [hround] using kappa_mean P m

theorem first_mean (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    mean (fun s : State => indicator (firstBad P m (SelectedChallengeMap.sigma 29 s))) ≤
      foldBudget := by
  cases h : readFirst P m with
  | none =>
      simp only [firstBad, h, indicator_false, mean_const]
      exact foldBudget_nonneg
  | some v =>
      simpa only [firstBad, h, foldBudget] using
        SelectedOpeningEventMass.first_mass v.context.word v.context.functionals v.context.baseFunctional v.payload v.gamma v.kappa

theorem row29_density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 29) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m (firstBad P m) v.2)) ≤
      foldBudget := by
  apply LiteralOrdinaryDensity.density P m (firstBad P m) foldBudget
  · omega
  · exact foldBudget_nonneg
  · simpa only [hround] using first_mean P m

theorem second_mean (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) :
    mean (fun s : State => indicator (secondBad P m (SelectedChallengeMap.sigma 30 s))) ≤
      foldBudget := by
  cases h : readSecond P m with
  | none =>
      simp only [secondBad, h, indicator_false, mean_const]
      exact foldBudget_nonneg
  | some v =>
      simpa only [secondBad, h, foldBudget] using
        SelectedOpeningEventMass.second_mass v.context.word v.word v.context.functionals v.context.baseFunctional v.payload v.gamma v.kappa v.alpha0

theorem row30_density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 30) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m (secondBad P m) v.2)) ≤
      foldBudget := by
  apply LiteralOrdinaryDensity.density P m (secondBad P m) foldBudget
  · omega
  · exact foldBudget_nonneg
  · simpa only [hround] using second_mean P m

#print axioms gamma_mean
#print axioms row27_density
#print axioms kappa_mean
#print axioms row28_density
#print axioms first_mean
#print axioms row29_density
#print axioms second_mean
#print axioms row30_density

end AspisR1.LiteralOpeningDensity
end

