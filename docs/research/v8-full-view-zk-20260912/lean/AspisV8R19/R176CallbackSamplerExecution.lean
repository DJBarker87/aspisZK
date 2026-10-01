import AspisR156FullFreeze.FunsSample
import AspisV8R19.R173NonzeroExecution

set_option autoImplicit false
namespace AspisV8R19.R176CallbackSamplerExecution
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core
open R167TranscriptPrimitiveExecution

abbrev Output := core.result.Result field.QM31 AspisR156FullFreeze.Error ×
  transcript.Transcript

def callbackOutcome : core.result.Result field.QM31 Unit →
    core.result.Result field.QM31 AspisR156FullFreeze.Error
  | .Ok q => .Ok q
  | .Err _ => .Err .Sampler

def chosen (t : transcript.Transcript) (nonzero : Bool) :
    Result (core.result.Result field.QM31 Unit × transcript.Transcript) :=
  if nonzero then transcript.Transcript.challenge_nonzero_qm31 t
  else transcript.Transcript.challenge_qm31 t

theorem sample_factored (t : transcript.Transcript) (nonzero : Bool) :
    sample t nonzero = (do
      let (r,next) ← chosen t nonzero
      ok (callbackOutcome r,next)) := by
  cases nonzero with
  | false =>
    simp only [sample,chosen,Bool.false_eq_true,if_false]
    cases h : transcript.Transcript.challenge_qm31 t with
    | fail e => simp
    | div => simp
    | ok pair =>
      rcases pair with ⟨r,next⟩
      cases r <;> rfl
  | true =>
    simp only [sample,chosen,if_true]
    cases h : transcript.Transcript.challenge_nonzero_qm31 t with
    | fail e => simp
    | div => simp
    | ok pair =>
      rcases pair with ⟨r,next⟩
      cases r <;> rfl

noncomputable section
open DuplexFrames SourceDuplexStep

def modelRun (H : Bytes → State) (nonzero : Bool) (s : State) :
    MemoizedProgramLaw.View Bytes State
      (core.result.Result field.QM31 AspisR156FullFreeze.Error × State) :=
  if nonzero then
    let run := SamplerWrapperPolicies.nonzeroRun H s
    (run.1,(callbackOutcome (R170LimbSamplerExecution.outcome
      (R139NonzeroModelBridge.encodePolicyResult run.2.1)),run.2.2))
  else
    let run := QM31SamplerProgram.challengeRun H s
    (run.1,(callbackOutcome (R170LimbSamplerExecution.encodeResult run.2.1),run.2.2))

def encodeOutput (H : Bytes → State)
    (r : core.result.Result field.QM31 AspisR156FullFreeze.Error × State) : Output :=
  (r.1,transcriptFor H r.2)

theorem sample_exact (H : Bytes → State) (nonzero : Bool) (s : State) :
    sample (transcriptFor H s) nonzero =
      .ok (encodeOutput H (modelRun H nonzero s).2) := by
  rw [sample_factored]
  cases nonzero with
  | false =>
    simp only [chosen,Bool.false_eq_true,if_false,
      R170LimbSamplerExecution.challenge_exact,bind_tc_ok,modelRun,encodeOutput]
  | true =>
    simp only [chosen,if_true,R173NonzeroExecution.challenge_exact,
      bind_tc_ok,modelRun,encodeOutput]

#print axioms sample_exact
end
#print axioms sample_factored
end AspisV8R19.R176CallbackSamplerExecution
