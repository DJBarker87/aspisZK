import R1LiteralClassifier

/-! Identify the literal row-32 rho event with its residual-polynomial
predicate when the completed matching-data and ordered-query readers succeed.
This is a conditional event identity only; it makes no probability,
acceptance, or extraction claim. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralRhoBinding

open AspisR1.LiteralTranscript
open AspisR1.TranscriptView
open AspisR1.LiteralClassifier
open AspisR1.LiteralRhoDensity
open AspisR1.LiteralQueryRead
open AspisR1.LiteralMatchingData
open AspisR1.SelectedChallengeMap
open AspisR1.QueryResidualBridge

attribute [local irreducible] QueryResidualBridge.rhoBad

theorem rho_event_iff
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (v : AspisWideTower.WideExact)
    (state : AspisV8R19.SourceDuplexStep.State)
    (d : AspisR1.MatchingSupport.Data AspisWideTower.WideExact)
    (q : Fin 22 → Fin 262144)
    (hround : P.round = 32)
    (hvalid : LiteralTranscript.valid 32 m)
    (hdata : LiteralMatchingData.beforeRho P = some d)
    (hqueries : LiteralQueryRead.queriesAt P.rounds 31 = some q) :
    LiteralClassifier.bad P m (TranscriptView.Value.ordinary v, state) ↔
      SelectedChallengeMap.rhoOf v ∈
        QueryResidualBridge.rhoBad LiteralOpeningView.eK d q := by
  have hread : LiteralRhoDensity.read P = some (d, q) := by
    simp [LiteralRhoDensity.read, hdata, hqueries]
  cases m with
  | initial root word => simp [LiteralTranscript.valid] at hvalid
  | c2 bytes word => simp [LiteralTranscript.valid] at hvalid
  | second bytes word => simp [LiteralTranscript.valid] at hvalid
  | payload bytes =>
      simpa [LiteralClassifier.bad, LiteralOrdinaryDensity.event,
        LiteralTranscript.valid, LiteralRhoDensity.bad, hround, hvalid, hread]

#print axioms rho_event_iff

end AspisR1.LiteralRhoBinding
end
