import AspisV8R19.SamplerObservedChallenge

/-! Expose only query/answer bytes, the sampled result/error and state bytes.
The internal backend function pointer is not part of the observed view.
This exact interpreter correspondence is not a full transcript privacy law. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedProgram
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerObservation SamplerLimbBridge SamplerChallengeBridge
open SqueezeOracleBridge SourceDuplexStep DuplexFrames

def decodeResult : core.result.Result field.QM31 transcript.ChallengeSampleExhausted → Option (List Nat)
  | .Err _ => none
  | .Ok q => some [q.c0.a.val,q.c0.b.val,q.c1.a.val,q.c1.b.val]

theorem result_roundtrip (H : Bytes → State) (s : State) :
    decodeResult (encodeResult (QM31SamplerProgram.challengeRun H s).2.1) =
      (QM31SamplerProgram.challengeRun H s).2.1 := by
  cases hm : (QM31SamplerProgram.challengeRun H s).2.1 with
  | none => rfl
  | some xs =>
      obtain ⟨hlen,hcan⟩ := QM31SamplerInvariants.challenge_four_canonical_limbs H s xs hm
      obtain ⟨a,b,c,d,hxs⟩ : ∃ a b c d, xs=[a,b,c,d] :=
        ⟨_,_,_,_,List.eq_getElem_of_length_eq_four xs hlen⟩
      subst xs
      have ha := hcan a (by simp)
      have hb := hcan b (by simp)
      have hc := hcan c (by simp)
      have hd := hcan d (by simp)
      simp only [encodeResult,decodeResult,word_value a (by omega),word_value b (by omega),
        word_value c (by omega),word_value d (by omega)]

def observe (H : Bytes → State) (s : State) (history : Trace) := do
  let ((result,next),t) ← SamplerObservedSource.challenge_qm31 (transcriptFor H s) history
  ok (decodeTrace t,(decodeResult result,decodeState next.state))

theorem public_view (H : Bytes → State) (s : State) (history : Trace) :
    observe H s history =
      .ok (decodeTrace history++(QM31SamplerProgram.challengeRun H s).1,
        (QM31SamplerProgram.challengeRun H s).2) := by
  obtain ⟨t,he,ht⟩ := SamplerObservedChallenge.challenge_trace H s history
  unfold observe
  erw [he]
  simp only [bind_tc_ok,ht,result_roundtrip,transcriptFor,state_roundtrip]

theorem oracle_program (H : Bytes → State) (s : State) :
    observe H s [] = .ok (MemoizedProgramLaw.eval H (QM31SamplerProgram.challengeProgram s)) := by
  simpa only [QM31SamplerProgram.challenge_exact,decodeTrace,List.map_nil,List.nil_append] using
    public_view H s []

#print axioms result_roundtrip
#print axioms public_view
#print axioms oracle_program
end AspisV8R19.SamplerObservedProgram
