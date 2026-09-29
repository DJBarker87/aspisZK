import AspisV8R19.SamplerChallengeBridge
import AspisV8R19.SamplerClosureCircleSourceExecution

/-! The complete extracted circle sampler's value/error/state equals the
retained bounded-wrapper algorithm with the actual source error constructors.
This theorem uses a total deterministic hash adapter. It does not identify
the source's observed hash-query trace with the model's trace projection. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerCircleBridge
open Aeneas Aeneas.Std Result AspisR72Sampler
open DuplexFrames SourceDuplexStep SqueezeOracleBridge
open AspisV8R15.ExactTowerBase
open SamplerClosureProductCorrectness (decode Canonical)
open SamplerClosureCircleSourceExecution (encodePoint decodePoint)
noncomputable section

def modelRun (H : Bytes → State) (n : Nat) (s : State) :=
  BoundedSamplerWrapper.run SamplerCirclePolicy.accept
    transcript.CirclePointSampleError.ChallengeSampleExhausted
    transcript.CirclePointSampleError.ParameterSampleExhausted H n s

def encodeResult : Except transcript.CirclePointSampleError (QM31Exact × QM31Exact) →
    core.result.Result circle.SecureCirclePoint transcript.CirclePointSampleError
  | .error e => .Err e
  | .ok p => .Ok (encodePoint p)

theorem decode_words (a b c d : Nat)
    (ha : a < 2147483647) (hb : b < 2147483647)
    (hc : c < 2147483647) (hd : d < 2147483647) :
    decode {c0 := {a := SamplerLimbBridge.encodeWord a, b := SamplerLimbBridge.encodeWord b},
            c1 := {a := SamplerLimbBridge.encodeWord c, b := SamplerLimbBridge.encodeWord d}} =
      SamplerFieldDecode.decode [a,b,c,d] := by
  simp only [decode,SamplerFieldDecode.decode,SamplerFieldDecode.decode4,
    SamplerLimbBridge.word_value a (by omega),SamplerLimbBridge.word_value b (by omega),
    SamplerLimbBridge.word_value c (by omega),SamplerLimbBridge.word_value d (by omega)]

theorem bounded_exact (H : Bytes → State) (n : Nat) (s : State) :
    SamplerOuterExecution.bounded n (transcriptFor H s) =
      .ok (encodeResult (modelRun H n s).2.1,transcriptFor H (modelRun H n s).2.2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      cases hr : (QM31SamplerProgram.challengeRun H s).2.1 with
      | none =>
          simp only [SamplerOuterExecution.bounded,SamplerChallengeBridge.challenge_exhaustion H s hr,
            bind_tc_ok,modelRun,BoundedSamplerWrapper.run,hr,encodeResult]
      | some xs =>
          obtain ⟨hlen,hcan⟩ := QM31SamplerInvariants.challenge_four_canonical_limbs H s xs hr
          obtain ⟨a,b,c,d,hxs⟩ : ∃ a b c d, xs=[a,b,c,d] :=
            ⟨_,_,_,_,List.eq_getElem_of_length_eq_four xs hlen⟩
          subst xs
          have hs := SamplerChallengeBridge.challenge_success H s a b c d hr
          have hc := SamplerChallengeBridge.successful_value_canonical H s _ _ hs
          have hdecode := decode_words a b c d (hcan a (by simp)) (hcan b (by simp))
            (hcan c (by simp)) (hcan d (by simp))
          simp only [SamplerOuterExecution.bounded,hs,bind_tc_ok]
          rw [SamplerClosureCircleSourceExecution.source_execution _ hc,hdecode]
          cases hp : SamplerCirclePolicy.pureMap (SamplerFieldDecode.decode [a,b,c,d]) with
          | error e =>
              simpa only [hp,SamplerClosureCircleSourceExecution.encodeResult,bind_tc_ok,
                modelRun,BoundedSamplerWrapper.run,hr,SamplerCirclePolicy.accept,Except.toOption] using
                ih (QM31SamplerProgram.challengeRun H s).2.2
          | ok p =>
              simp only [hp,SamplerClosureCircleSourceExecution.encodeResult,bind_tc_ok,
                modelRun,BoundedSamplerWrapper.run,hr,SamplerCirclePolicy.accept,Except.toOption,
                encodeResult]

theorem source_exact (H : Bytes → State) (s : State) :
    transcript.Transcript.challenge_secure_circle_point (transcriptFor H s) =
      .ok (encodeResult (modelRun H 3 s).2.1,transcriptFor H (modelRun H 3 s).2.2) := by
  rw [SamplerOuterExecution.entry_three,bounded_exact]

theorem source_no_failure (H : Bytes → State) (s : State) (e : Error) :
    transcript.Transcript.challenge_secure_circle_point (transcriptFor H s) ≠ .fail e := by
  rw [source_exact]; simp

theorem successful_circle (H : Bytes → State) (s : State)
    (p : circle.SecureCirclePoint) (next : transcript.Transcript)
    (h : transcript.Transcript.challenge_secure_circle_point (transcriptFor H s)=.ok (.Ok p,next)) :
    Canonical p.x ∧ Canonical p.y ∧ (decode p.x)^2+(decode p.y)^2=1 ∧
      ¬ ((decode p.x).im=0 ∧ (decode p.y).im=0) := by
  rw [source_exact] at h
  cases hm : (modelRun H 3 s).2.1 with
  | error e => simp [hm,encodeResult] at h
  | ok q =>
      have he : encodePoint q=p := by
        have pair : encodePoint q=p ∧ transcriptFor H (modelRun H 3 s).2.2=next := by
          simpa only [hm,encodeResult,Result.ok.injEq,Prod.mk.injEq,core.result.Result.Ok.injEq] using h
        exact pair.1
      subst p
      obtain ⟨xs,_,_,ha⟩ := BoundedSamplerWrapper.successful_image _ _ _ H 3 s q hm
      obtain ⟨hout,hd,hq⟩ := SamplerCirclePolicy.accept_policy xs q ha
      refine ⟨(SamplerClosureCircleSourceExecution.point_canonical q).1,
        (SamplerClosureCircleSourceExecution.point_canonical q).2,?_,?_⟩
      · change (decode (SamplerClosureProductExecution.encode q.1))^2+
          (decode (SamplerClosureProductExecution.encode q.2))^2=1
        rw [SamplerClosureProductCorrectness.decode_encode,SamplerClosureProductCorrectness.decode_encode,hq]
        exact SamplerCirclePolicy.point_on_circle _ hd
      · change ¬ ((decode (SamplerClosureProductExecution.encode q.1)).im=0 ∧
          (decode (SamplerClosureProductExecution.encode q.2)).im=0)
        rw [SamplerClosureProductCorrectness.decode_encode,SamplerClosureProductCorrectness.decode_encode,hq]
        exact SamplerCirclePolicy.outside_point _ hout

#print axioms decode_words
#print axioms bounded_exact
#print axioms source_exact
#print axioms source_no_failure
#print axioms successful_circle
end
end AspisV8R19.SamplerCircleBridge
