import AspisV8R19.R171SamplerCanonical

set_option autoImplicit false
namespace AspisV8R19.R172CircleSamplerExecution
open Aeneas Aeneas.Std Result ControlFlow
open AspisR156FullFreeze.aspis_core

abbrev Output := core.result.Result circle.SecureCirclePoint
  transcript.CirclePointSampleError × transcript.Transcript

def bounded : Nat → transcript.Transcript → Result Output
  | 0,s => .ok (.Err .ParameterSampleExhausted,s)
  | n+1,s => do
    let (r,s1) ← transcript.Transcript.challenge_qm31 s
    match r with
    | .Err _ => ok (.Err .ChallengeSampleExhausted,s1)
    | .Ok q =>
      let point ← circle.secure_ood_circle_point_from_parameter q
      match point with
      | .Ok p => ok (.Ok p,s1)
      | .Err _ => bounded n s1

theorem body_factored (r : core.ops.range.Range U32) (s : transcript.Transcript) :
    transcript.Transcript.challenge_secure_circle_point_loop.body r s = (do
      let (o,r1) ← core.iter.range.IteratorRange.next core.iter.range.StepU32 r
      match o with
      | none => ok (.done (.Err .ParameterSampleExhausted,s))
      | some _ =>
        let (sample,s1) ← transcript.Transcript.challenge_qm31 s
        match sample with
        | .Err _ => ok (.done (.Err .ChallengeSampleExhausted,s1))
        | .Ok q =>
          let point ← circle.secure_ood_circle_point_from_parameter q
          match point with
          | .Ok p => ok (.done (.Ok p,s1))
          | .Err _ => ok (.cont (r1,s1))) := by
  simp only [transcript.Transcript.challenge_secure_circle_point_loop.body]
  congr 1
  funext x
  rcases x with ⟨o,r1⟩
  cases o with
  | none => rfl
  | some v =>
    simp only []
    congr 1
    funext x
    rcases x with ⟨sample,s1⟩
    cases sample with
    | Ok q => rfl
    | Err e => rfl

theorem loop_execution (n : Nat) (r : core.ops.range.Range U32)
    (s : transcript.Transcript) (hn : r.end.val-r.start.val=n) :
    transcript.Transcript.challenge_secure_circle_point_loop r s = bounded n s := by
  induction n generalizing r s with
  | zero =>
    have hr : ¬ r.start.val < r.end.val := by omega
    rw [transcript.Transcript.challenge_secure_circle_point_loop,loop.eq_def]
    simp only [body_factored,SamplerOuterExecution.range_next,dif_neg hr,bind_tc_ok,bounded]
  | succ n ih =>
    have hr : r.start.val < r.end.val := by omega
    have hn' : (R137SamplerInnerStep.nextRange r hr).end.val -
        (R137SamplerInnerStep.nextRange r hr).start.val = n := by
      change r.end.val - (r.start.val+1) = n
      omega
    rw [transcript.Transcript.challenge_secure_circle_point_loop,loop.eq_def]
    simp only [body_factored,SamplerOuterExecution.range_next,dif_pos hr,bind_tc_ok,bounded]
    cases hs : transcript.Transcript.challenge_qm31 s with
    | fail e => simp [hs]
    | div => simp [hs]
    | ok x =>
      rcases x with ⟨sample,s1⟩
      cases sample with
      | Err e => rfl
      | Ok q =>
        simp only [bind_tc_ok]
        cases hp : circle.secure_ood_circle_point_from_parameter q with
        | fail e => simp [hp]
        | div => simp [hp]
        | ok result =>
          cases result with
          | Ok p => rfl
          | Err e =>
            simpa only [bind_tc_ok,transcript.Transcript.challenge_secure_circle_point_loop,
              body_factored,SamplerOuterExecution.range_next,R137SamplerInnerStep.nextRange]
              using ih (R137SamplerInnerStep.nextRange r hr) s1 hn'

theorem three_attempts (s : transcript.Transcript) :
    transcript.Transcript.challenge_secure_circle_point s = bounded 3 s := by
  unfold transcript.Transcript.challenge_secure_circle_point
  apply loop_execution 3
  simp only [transcript.CIRCLE_POINT_RETRY_LIMIT]
  rfl

noncomputable section
open SourceDuplexStep DuplexFrames

def pureBounded (H : Bytes → State) : Nat → State →
    core.result.Result circle.SecureCirclePoint transcript.CirclePointSampleError × State
  | 0,s => (.Err .ParameterSampleExhausted,s)
  | n+1,s =>
    let draw := QM31SamplerProgram.challengeRun H s
    let next := draw.2.2
    match R170LimbSamplerExecution.encodeResult draw.2.1 with
    | .Err _ => (.Err .ChallengeSampleExhausted,next)
    | .Ok q =>
      match R166CircleExecution.encodeResult
        (SamplerCirclePolicy.pureMap (R165QuarticExecution.decode q)) with
      | .Ok p => (.Ok p,next)
      | .Err _ => pureBounded H n next

def encodeOutput (H : Bytes → State)
    (x : core.result.Result circle.SecureCirclePoint transcript.CirclePointSampleError × State) :
    Output := (x.1,R167TranscriptPrimitiveExecution.transcriptFor H x.2)

theorem bounded_exact (H : Bytes → State) (n : Nat) (s : State) :
    bounded n (R167TranscriptPrimitiveExecution.transcriptFor H s) =
      .ok (encodeOutput H (pureBounded H n s)) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [bounded,R170LimbSamplerExecution.challenge_exact,bind_tc_ok,pureBounded]
    cases hr : R170LimbSamplerExecution.encodeResult
      (QM31SamplerProgram.challengeRun H s).2.1 with
    | Err e => rfl
    | Ok q =>
      have hq : transcript.Transcript.challenge_qm31
          (R167TranscriptPrimitiveExecution.transcriptFor H s) =
          .ok (.Ok q,R167TranscriptPrimitiveExecution.transcriptFor H
            (QM31SamplerProgram.challengeRun H s).2.2) := by
        rw [R170LimbSamplerExecution.challenge_exact,hr]
      have hc := R171SamplerCanonical.successful_canonical H s q _ hq
      simp only []
      rw [R166CircleExecution.source_execution q hc]
      cases hp : R166CircleExecution.encodeResult
        (SamplerCirclePolicy.pureMap (R165QuarticExecution.decode q)) with
      | Ok p => rfl
      | Err e =>
        simpa only [bind_tc_ok] using ih (QM31SamplerProgram.challengeRun H s).2.2

theorem challenge_exact (H : Bytes → State) (s : State) :
    transcript.Transcript.challenge_secure_circle_point
        (R167TranscriptPrimitiveExecution.transcriptFor H s) =
      .ok (encodeOutput H (pureBounded H 3 s)) := by
  rw [three_attempts,bounded_exact]

#print axioms bounded_exact
#print axioms challenge_exact
end
#print axioms body_factored
#print axioms loop_execution
#print axioms three_attempts
end AspisV8R19.R172CircleSamplerExecution
