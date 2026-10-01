import AspisV8R19.R172CircleSamplerExecution
import AspisV8R19.SamplerCircleBridge
import AspisV8R19.R139NonzeroModelBridge

set_option autoImplicit false
namespace AspisV8R19.R177CircleScheduleBridge

open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase

def encodeScheduleResult :
    Except AspisR72Sampler.transcript.CirclePointSampleError
      (QM31Exact × QM31Exact) →
    core.result.Result circle.SecureCirclePoint transcript.CirclePointSampleError
  | .error .ChallengeSampleExhausted => .Err .ChallengeSampleExhausted
  | .error .ParameterSampleExhausted => .Err .ParameterSampleExhausted
  | .ok p => .Ok (R166CircleExecution.encodePoint p)

theorem encodeWord_adapter (n : Nat) :
    R137SamplerLimbBridge.encodeWord n = SamplerLimbBridge.encodeWord n := by
  rfl

theorem quartic_adapter (a b c d : Nat) :
    R170LimbSamplerExecution.quartic
      (R139NonzeroModelBridge.encodeQM31 a b c d) =
    { c0 := { a := SamplerLimbBridge.encodeWord a,
              b := SamplerLimbBridge.encodeWord b },
      c1 := { a := SamplerLimbBridge.encodeWord c,
              b := SamplerLimbBridge.encodeWord d } } := by
  simp only [R170LimbSamplerExecution.quartic,
    R139NonzeroModelBridge.encodeQM31, encodeWord_adapter]

theorem decode_words (a b c d : Nat)
    (ha : a < 2147483647) (hb : b < 2147483647)
    (hc : c < 2147483647) (hd : d < 2147483647) :
    R165QuarticExecution.decode
      (R170LimbSamplerExecution.quartic
        (R139NonzeroModelBridge.encodeQM31 a b c d)) =
      SamplerFieldDecode.decode [a, b, c, d] := by
  rw [quartic_adapter]
  simpa only [R165QuarticExecution.decode, R165QuarticExecution.toOld,
    R165QuarticExecution.toOldCM] using
      SamplerCircleBridge.decode_words a b c d ha hb hc hd

theorem pureBounded_model (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (n : Nat) (s : SourceDuplexStep.State) :
    R172CircleSamplerExecution.pureBounded H n s =
      (encodeScheduleResult (SamplerCircleBridge.modelRun H n s).2.1,
        (SamplerCircleBridge.modelRun H n s).2.2) := by
  induction n generalizing s with
  | zero =>
      simp [R172CircleSamplerExecution.pureBounded,
        SamplerCircleBridge.modelRun, BoundedSamplerWrapper.run,
        encodeScheduleResult]
  | succ n ih =>
      cases hr : (QM31SamplerProgram.challengeRun H s).2.1 with
      | none =>
          simp [R172CircleSamplerExecution.pureBounded,
            R170LimbSamplerExecution.encodeResult,
            R170LimbSamplerExecution.outcome,
            R137SamplerChallengeBridge.encodeResult,
            SamplerCircleBridge.modelRun, BoundedSamplerWrapper.run,
            encodeScheduleResult, hr]
      | some xs =>
          obtain ⟨hlen, hcan⟩ :=
            QM31SamplerInvariants.challenge_four_canonical_limbs H s xs hr
          obtain ⟨a, b, c, d, hxs⟩ : ∃ a b c d, xs = [a, b, c, d] :=
            ⟨_, _, _, _, List.eq_getElem_of_length_eq_four xs hlen⟩
          subst xs
          have ha : a < 2147483647 := hcan a (by simp)
          have hb : b < 2147483647 := hcan b (by simp)
          have hc : c < 2147483647 := hcan c (by simp)
          have hd : d < 2147483647 := hcan d (by simp)
          have hquartic : R170LimbSamplerExecution.encodeResult
              (some [a, b, c, d]) =
              .Ok (R170LimbSamplerExecution.quartic
                (R139NonzeroModelBridge.encodeQM31 a b c d)) := rfl
          have hdecode := decode_words a b c d ha hb hc hd
          simp only [R172CircleSamplerExecution.pureBounded,
            SamplerCircleBridge.modelRun, BoundedSamplerWrapper.run,
            hr, hquartic]
          rw [hdecode]
          cases hp : SamplerCirclePolicy.pureMap
              (SamplerFieldDecode.decode [a, b, c, d]) with
          | error e =>
              cases e with
              | singular =>
                  simpa [hp, R166CircleExecution.encodeResult,
                    R166CircleExecution.encodeError,
                    SamplerCirclePolicy.accept, Except.toOption,
                    SamplerCircleBridge.modelRun, encodeScheduleResult] using
                    ih (QM31SamplerProgram.challengeRun H s).2.2
              | subfield =>
                  simpa [hp, R166CircleExecution.encodeResult,
                    R166CircleExecution.encodeError,
                    SamplerCirclePolicy.accept, Except.toOption,
                    SamplerCircleBridge.modelRun, encodeScheduleResult] using
                    ih (QM31SamplerProgram.challengeRun H s).2.2
          | ok p =>
              simp [hp, R166CircleExecution.encodeResult,
                SamplerCirclePolicy.accept, Except.toOption,
                    SamplerCircleBridge.modelRun, encodeScheduleResult]

theorem challenge_schedule_exact
    (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (s : SourceDuplexStep.State) :
    transcript.Transcript.challenge_secure_circle_point
        (R167TranscriptPrimitiveExecution.transcriptFor H s) =
      .ok (R172CircleSamplerExecution.encodeOutput H
        (encodeScheduleResult (SamplerCircleBridge.modelRun H 3 s).2.1,
          (SamplerCircleBridge.modelRun H 3 s).2.2)) := by
  rw [R172CircleSamplerExecution.challenge_exact, pureBounded_model]

#print axioms encodeWord_adapter
#print axioms quartic_adapter
#print axioms decode_words
#print axioms pureBounded_model
#print axioms challenge_schedule_exact
end AspisV8R19.R177CircleScheduleBridge
