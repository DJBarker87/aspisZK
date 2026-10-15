import R1LiteralSemanticMessageFacts
import R1UnifiedSamplerLaw
import R1SelectedTranscriptParams
import AspisV8R19.R572SequentialWordMass

/-! Lift an arbitrary ordinary-challenge density bound to the literal-message
sampler on any row other than the query row. This is sampler plumbing only. -/

set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralOrdinaryDensity

open FS FS2
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.SourceDuplexStep
open AspisV8R19.R572SequentialWordMass
attribute [local instance] Classical.propDecidable

def event (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (bad : AspisWideTower.WideExact → Prop)
    (ch : LiteralTranscript.Challenge) : Prop :=
  LiteralTranscript.valid P.round m ∧
    match ch.1 with
    | .ordinary value => bad value
    | .queries _ => False

theorem density (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message)
    (bad : AspisWideTower.WideExact → Prop) (eps : ℚ)
    (hi : P.round ≠ 31) (hne : 0 ≤ eps)
    (hmass : mean (fun s : State =>
      indicator (bad (AspisR1.SelectedChallengeMap.sigma P.round s))) ≤ eps) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (event P m bad v.2)) ≤ eps := by
  by_cases hv : LiteralTranscript.valid P.round m
  · have hverase := LiteralSemanticMessageFacts.valid_erased P.round m hv
    unfold LiteralTranscript.samp
    rw [UnifiedSampler.unified_law SelectedTranscriptParams.params _ P.round
      (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)
      (fun ch => indicator (event P m bad ch)) hi hverase]
    simpa only [event, hv, true_and, TranscriptView.liftChallenge, SelectedTranscriptParams.params_sigma,
      mean_const] using hmass
  · simp only [event, hv, false_and, indicator_false, independentMean_const]
    exact hne

#print axioms density

end AspisR1.LiteralOrdinaryDensity
end
