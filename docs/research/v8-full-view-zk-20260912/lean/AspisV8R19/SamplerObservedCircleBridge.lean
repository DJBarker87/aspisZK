import AspisV8R19.SamplerObservedCircleLoop
import AspisV8R19.SamplerCircleBridge

/-! Ordered source observations for all bounded secure-circle retries. The
same total deterministic hash adapter is reused across attempts; no fresh
answers are substituted. This is not a random-oracle security theorem. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedCircleBridge
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerObservation SamplerObservedLaws
open DuplexFrames SourceDuplexStep SqueezeOracleBridge
open SamplerCircleBridge (modelRun encodeResult decode_words)
noncomputable section

theorem bounded_trace (H : Bytes → State) (n : Nat) (s : State) (history : Trace) :
    ∃ observed, SamplerObservedCircleLoop.bounded n (transcriptFor H s) history =
      .ok ((encodeResult (modelRun H n s).2.1,
        transcriptFor H (modelRun H n s).2.2),observed) ∧
      decodeTrace observed=decodeTrace history++(modelRun H n s).1 := by
  induction n generalizing s history with
  | zero => exact ⟨history,rfl,(List.append_nil _).symm⟩
  | succ n ih =>
      obtain ⟨calls,he,ht⟩ := SamplerObservedChallenge.challenge_trace H s history
      cases hr : (QM31SamplerProgram.challengeRun H s).2.1 with
      | none =>
          refine ⟨calls,?_,?_⟩
          · simp only [SamplerObservedCircleLoop.bounded,bind_apply,he,bind_tc_ok,
              SamplerChallengeBridge.encodeResult,hr,pure_apply,
              modelRun,BoundedSamplerWrapper.run,encodeResult]
          · simpa only [modelRun,BoundedSamplerWrapper.run,hr] using ht
      | some xs =>
          obtain ⟨hlen,hcan⟩ := QM31SamplerInvariants.challenge_four_canonical_limbs H s xs hr
          obtain ⟨a,b,c,d,hxs⟩ : ∃ a b c d, xs=[a,b,c,d] :=
            ⟨_,_,_,_,List.eq_getElem_of_length_eq_four xs hlen⟩
          subst xs
          have hs := SamplerChallengeBridge.challenge_success H s a b c d hr
          have hc := SamplerChallengeBridge.successful_value_canonical H s _ _ hs
          have hd := decode_words a b c d (hcan a (by simp)) (hcan b (by simp))
            (hcan c (by simp)) (hcan d (by simp))
          cases hp : SamplerCirclePolicy.pureMap (SamplerFieldDecode.decode [a,b,c,d]) with
          | error e =>
              obtain ⟨observed,ho,hto⟩ := ih (QM31SamplerProgram.challengeRun H s).2.2 calls
              refine ⟨observed,?_,?_⟩
              · simpa only [SamplerObservedCircleLoop.bounded,bind_apply,he,bind_tc_ok,
                  SamplerChallengeBridge.encodeResult,hr,lift_apply,
                  SamplerClosureCircleSourceExecution.source_execution _ hc,hd,hp,
                  SamplerClosureCircleSourceExecution.encodeResult,
                  modelRun,BoundedSamplerWrapper.run,SamplerCirclePolicy.accept,Except.toOption] using ho
              · simpa only [modelRun,BoundedSamplerWrapper.run,hr,SamplerCirclePolicy.accept,hp,
                  Except.toOption,ht,List.append_assoc] using hto
          | ok p =>
              refine ⟨calls,?_,?_⟩
              · simp only [SamplerObservedCircleLoop.bounded,bind_apply,he,bind_tc_ok,
                  SamplerChallengeBridge.encodeResult,hr,lift_apply,
                  SamplerClosureCircleSourceExecution.source_execution _ hc,hd,hp,
                  SamplerClosureCircleSourceExecution.encodeResult,pure_apply,
                  modelRun,BoundedSamplerWrapper.run,SamplerCirclePolicy.accept,Except.toOption,encodeResult]
              · simpa only [modelRun,BoundedSamplerWrapper.run,hr,SamplerCirclePolicy.accept,hp,
                  Except.toOption] using ht

theorem source_trace (H : Bytes → State) (s : State) (history : Trace) :
    ∃ observed, SamplerObservedSource.challenge_secure_circle_point (transcriptFor H s) history =
      .ok ((encodeResult (modelRun H 3 s).2.1,
        transcriptFor H (modelRun H 3 s).2.2),observed) ∧
      decodeTrace observed=decodeTrace history++(modelRun H 3 s).1 := by
  rw [SamplerObservedCircleLoop.entry_three]
  exact bounded_trace H 3 s history

theorem source_erasure (H : Bytes → State) (s : State) (history : Trace) :
    (do let (out,_) ← SamplerObservedSource.challenge_secure_circle_point (transcriptFor H s) history
        ok out) = transcript.Transcript.challenge_secure_circle_point (transcriptFor H s) := by
  obtain ⟨t,he,_⟩ := source_trace H s history
  rw [he,SamplerCircleBridge.source_exact]
  rfl

#print axioms bounded_trace
#print axioms source_trace
#print axioms source_erasure
end
end AspisV8R19.SamplerObservedCircleBridge
