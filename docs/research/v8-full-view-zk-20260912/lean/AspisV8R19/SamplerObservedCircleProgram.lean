import AspisV8R19.SamplerObservedCircleBridge
import AspisV8R19.CachedFiniteSupport

/-! Complete public circle-sampler view and its memoized ideal-oracle law.
Includes arbitrary prior cached answers, repetitions, retries and exhaustion.
The source instrumentation and total adapter remain explicit boundaries. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedCircleProgram
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerObservation DuplexFrames SourceDuplexStep SqueezeOracleBridge
open SamplerCircleBridge (modelRun encodeResult)
open SamplerClosureCircleSourceExecution (decodePoint)
open AspisV8R15.ExactTowerBase
open MemoizedProgramLaw OracleFiniteSupport OracleResampling
noncomputable section

def decodeResult : core.result.Result circle.SecureCirclePoint transcript.CirclePointSampleError →
    Except transcript.CirclePointSampleError (QM31Exact × QM31Exact)
  | .Err e => .error e
  | .Ok p => .ok (decodePoint p)

theorem result_roundtrip (r : Except transcript.CirclePointSampleError (QM31Exact × QM31Exact)) :
    decodeResult (encodeResult r)=r := by
  cases r <;> simp only [decodeResult,encodeResult,SamplerClosureCircleSourceExecution.decode_point]

def observe (H : Bytes → State) (s : State) (history : Trace) := do
  let ((result,next),t) ← SamplerObservedSource.challenge_secure_circle_point (transcriptFor H s) history
  ok (decodeTrace t,(decodeResult result,decodeState next.state))

def program (s : State) := BoundedSamplerWrapper.program SamplerCirclePolicy.accept
  transcript.CirclePointSampleError.ChallengeSampleExhausted
  transcript.CirclePointSampleError.ParameterSampleExhausted 3 s

theorem public_view (H : Bytes → State) (s : State) (history : Trace) :
    observe H s history = .ok (decodeTrace history++(modelRun H 3 s).1,(modelRun H 3 s).2) := by
  obtain ⟨t,he,ht⟩ := SamplerObservedCircleBridge.source_trace H s history
  unfold observe
  erw [he]
  simp only [bind_tc_ok,ht,result_roundtrip,transcriptFor,state_roundtrip]

theorem oracle_program (H : Bytes → State) (s : State) :
    observe H s [] = .ok (eval H (program s)) := by
  rw [public_view]
  simp only [program,BoundedSamplerWrapper.exact_run,modelRun,decodeTrace,List.map_nil,List.nil_append]

theorem cached_oracle_law (s : State) (t : AspisV8PairedCommitment.Table Bytes State)
    (fallback : State) (test : Result (View Bytes State
      (Except transcript.CirclePointSampleError (QM31Exact × QM31Exact) × State)) → ℚ) :
    mean (fun H : {i // i ∈ support (program s)} → State =>
      test (observe (complete t (extend (support (program s)) H fallback)) s [])) =
      lazyMean (program s) t (fun view => test (.ok view)) := by
  simp only [oracle_program]
  exact CachedFiniteSupport.own_support_law (I := Bytes) (A := State)
    (O := Except transcript.CirclePointSampleError (QM31Exact × QM31Exact) × State)
    (program s) t fallback
    (fun view => test (.ok view))

#print axioms result_roundtrip
#print axioms public_view
#print axioms oracle_program
#print axioms cached_oracle_law
end
end AspisV8R19.SamplerObservedCircleProgram
