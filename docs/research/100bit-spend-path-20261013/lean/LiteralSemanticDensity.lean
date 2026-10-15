import R1LiteralSemanticView
import R1LiteralSemanticMessageFacts
import R1UnifiedSamplerLaw
import AspisV8R19.R572SequentialWordMass

/-! Semantic bad-event density for the actual literal-message sampler,
including initial and malformed-message branches. This is one component of
D2; the remaining row classes and terminal implication are separate. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.LiteralSemanticDensity

open FS FS2 R0P R0P.Mask R0P.SemSource
open AspisV8R19.SourceDuplexStep AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.R572SequentialWordMass
attribute [local instance] Classical.propDecidable

def event (B : PackBasis LiteralSemanticView.F) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (c : LiteralTranscript.Challenge) : Prop :=
  LiteralTranscript.valid P.round m ∧
    match c.1 with
    | .ordinary value => LiteralSemanticView.bad B P m value
    | .queries _ => False

theorem density (B : PackBasis LiteralSemanticView.F) (P : LiteralTranscript.Prefix)
    (m : LiteralTranscript.Message) (hi : P.round < 25) :
    independentMean (LiteralTranscript.samp P.round P m).toProgram
      (fun v => indicator (event B P m v.2)) ≤ combinedD2BudgetZ P.round := by
  by_cases hv : LiteralTranscript.valid P.round m
  · have hverase := LiteralSemanticMessageFacts.valid_erased P.round m hv
    unfold LiteralTranscript.samp
    rw [UnifiedSampler.unified_law SelectedTranscriptParams.params _ P.round
      (LiteralTranscript.erasePrefix P) (LiteralTranscript.erase m)
      (fun c => indicator (event B P m c)) (by omega) hverase]
    simpa only [event, hv, true_and, TranscriptView.liftChallenge,
      SelectedTranscriptParams.params_sigma, SelectedChallengeMap.semantic_row P.round hi,
      mean_const] using LiteralSemanticView.density B P m hi
  · simp only [event, hv, false_and, indicator_false, independentMean_const]
    exact combinedD2BudgetZ_nonneg P.round

#print axioms density

end AspisR1.LiteralSemanticDensity
end
