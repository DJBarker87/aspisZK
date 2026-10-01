import AspisV8R19.R170LimbSamplerExecution
import AspisV8R19.R166CircleExecution

set_option autoImplicit false
namespace AspisV8R19.R171SamplerCanonical
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open R170LimbSamplerExecution

theorem successful_canonical (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (s : SourceDuplexStep.State) (q : field.QM31) (next : transcript.Transcript)
    (h : transcript.Transcript.challenge_qm31
      (R167TranscriptPrimitiveExecution.transcriptFor H s) = .ok (.Ok q,next)) :
    R165QuarticExecution.Canonical q := by
  rw [challenge_exact] at h
  cases hr : R137SamplerChallengeBridge.encodeResult
    (QM31SamplerProgram.challengeRun H s).2.1 with
  | Err e => simp [encodeResult,hr,outcome] at h
  | Ok v =>
    have hc := R137SamplerChallengeBridge.successful_value_canonical H s v
      (R137TranscriptPrimitiveBridge.transcriptFor H
        (QM31SamplerProgram.challengeRun H s).2.2)
      (by rw [R137SamplerChallengeBridge.challenge_exact,hr])
    have hq : quartic v = q := by
      simpa only [encodeResult,hr,outcome,Result.ok.injEq,Prod.mk.injEq,
        core.result.Result.Ok.injEq] using (congrArg Prod.fst (Result.ok.inj h))
    subst q
    exact hc

#print axioms successful_canonical
end AspisV8R19.R171SamplerCanonical
