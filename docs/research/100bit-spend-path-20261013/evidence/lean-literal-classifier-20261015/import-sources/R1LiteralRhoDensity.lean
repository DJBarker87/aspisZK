import R1LiteralMatchingData
import R1LiteralQueryRead
import R1LiteralOrdinaryDensity
import R1RhoSamplerBound

/-! The row-32 residual event reads its matching data and ordered query list
from the completed literal prefix. Both are fixed before the fresh rho answer.
This is an independent-answer density theorem, not acceptance or extraction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralRhoDensity

open FS FS2
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.SourceDuplexStep
attribute [local instance] Classical.propDecidable

def read (P : LiteralTranscript.Prefix) :
    Option (MatchingSupport.Data AspisWideTower.WideExact × (Fin 22 → Fin 262144)) := do
  let d ← LiteralMatchingData.beforeRho P
  let q ← LiteralQueryRead.queriesAt P.rounds 31
  pure (d, q)

def bad (P : LiteralTranscript.Prefix) (v : AspisWideTower.WideExact) : Prop :=
  match read P with
  | none => False
  | some (d, q) => SelectedChallengeMap.rhoOf v ∈
      QueryResidualBridge.rhoBad LiteralOpeningView.eK d q

theorem budget_nonneg : 0 ≤ RhoSamplerBound.rhoCap := by
  unfold RhoSamplerBound.rhoCap
  positivity

theorem rho_mean (P : LiteralTranscript.Prefix) :
    mean (fun s : State => indicator (bad P (SelectedChallengeMap.sigma 32 s))) ≤
      RhoSamplerBound.rhoCap := by
  cases h : read P with
  | none =>
      simp only [bad, h, indicator_false, mean_const]
      exact budget_nonneg
  | some dq =>
      rcases dq with ⟨d, q⟩
      simp only [bad, h, SelectedChallengeMap.rho_row]
      exact RhoSamplerBound.modulo_bad_mass
        (by norm_num [AspisCircleGroupOrder.P]) SelectedSamplerRanks.stateRank
        R0P.SemSource.qm31Rank LiteralOpeningView.eK d q

theorem row32_density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (hround : P.round = 32) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (LiteralOrdinaryDensity.event P m (bad P) v.2)) ≤
      RhoSamplerBound.rhoCap := by
  apply LiteralOrdinaryDensity.density P m (bad P) RhoSamplerBound.rhoCap
  · omega
  · exact budget_nonneg
  · simpa only [hround] using rho_mean P

#print axioms rho_mean
#print axioms row32_density

end AspisR1.LiteralRhoDensity
end
