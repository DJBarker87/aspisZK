import AspisV8R19.SamplerObservedWriteback
import AspisV8R19.SamplerChallengeBridge

/-! Complete instrumented QM31 challenge value/error/state AND query trace.
The explicit instrumentation provenance remains a separate trust boundary. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedChallenge
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerLimbBridge
open SamplerLimbLoop (initialIter finish)
open SamplerObservation SamplerObservedLaws SamplerObservedWriteback
open SqueezeOracleBridge SamplerObservedSqueeze SourceDuplexStep DuplexFrames
open SamplerChallengeBridge (encodeResult)

theorem finish_model (H : Bytes → State) (c : QM31SamplerProgram.Cursor) (history : Trace) :
    ∃ observed, (do
      let (out,t) ← SamplerObservedLimbLoop.bounded 4 initialIter (fun it => it) (transcriptFor H c.state)
        (encodeState c.block) (SamplerInnerLoop.index (encodeCursor H c)) history
      let result ← finish out
      ok (result,t)) =
      .ok ((encodeResult (QM31SamplerProgram.limbsRun H 4 c).2.1,
        transcriptFor H (QM31SamplerProgram.limbsRun H 4 c).2.2.state),observed) ∧
      decodeTrace observed=decodeTrace history++(QM31SamplerProgram.limbsRun H 4 c).1 := by
  obtain ⟨t,hm,ht⟩ := bounded_matches H 4 c initialIter (fun it => it) (by rfl) history
  refine ⟨t,?_,ht⟩
  cases hx : (QM31SamplerProgram.limbsRun H 4 c).2.1 with
  | none =>
      simp only [Matches,hx] at hm
      obtain ⟨out,he⟩ := hm
      rw [he]
      simp only [bind_tc_ok,finish,encodeResult]
  | some values =>
      have hlen := QM31SamplerInvariants.accepted_limbs_length H 4 c values hx
      obtain ⟨a,b,v,d,hv⟩ : ∃ a b v d, values=[a,b,v,d] :=
        ⟨_,_,_,_,List.eq_getElem_of_length_eq_four values hlen⟩
      subst values
      simp only [Matches,hx] at hm
      rw [hm]
      simp only [bind_tc_ok,SamplerWriteback.finish_four,encodeResult]

theorem challenge_trace (H : Bytes → State) (s : State) (history : Trace) :
    ∃ observed, SamplerObservedSource.challenge_qm31 (transcriptFor H s) history =
      .ok ((encodeResult (QM31SamplerProgram.challengeRun H s).2.1,
        transcriptFor H (QM31SamplerProgram.challengeRun H s).2.2),observed) ∧
      decodeTrace observed=decodeTrace history++(QM31SamplerProgram.challengeRun H s).1 := by
  obtain ⟨t,hm,ht⟩ := finish_model H ⟨(step H s).2,(step H s).1,0⟩ (history++rawCalls H s)
  have hi : SamplerInnerLoop.index (encodeCursor H ⟨(step H s).2,(step H s).1,0⟩)=0#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [hi] at hm
  refine ⟨t,?_,?_⟩
  · rw [SamplerObservedLimbLoop.entry_four,adapter_execution]
    simp only [bind_tc_ok]
    simpa only [QM31SamplerProgram.challengeRun] using hm
  · simpa only [decode_append,raw_calls_decode,List.append_assoc,QM31SamplerProgram.challengeRun] using ht

theorem decoded_challenge (H : Bytes → State) (s : State) (history : Trace) :
    (do let (out,t) ← SamplerObservedSource.challenge_qm31 (transcriptFor H s) history
        ok (out,decodeTrace t)) =
      .ok ((encodeResult (QM31SamplerProgram.challengeRun H s).2.1,
        transcriptFor H (QM31SamplerProgram.challengeRun H s).2.2),
        decodeTrace history++(QM31SamplerProgram.challengeRun H s).1) := by
  obtain ⟨t,he,ht⟩ := challenge_trace H s history
  rw [he]
  simp only [bind_tc_ok,ht]

theorem challenge_erasure (H : Bytes → State) (s : State) (history : Trace) :
    (do let (out,_) ← SamplerObservedSource.challenge_qm31 (transcriptFor H s) history
        ok out) = transcript.Transcript.challenge_qm31 (transcriptFor H s) := by
  obtain ⟨t,he,_⟩ := challenge_trace H s history
  rw [he,SamplerChallengeBridge.challenge_exact]
  rfl

#print axioms finish_model
#print axioms challenge_trace
#print axioms decoded_challenge
#print axioms challenge_erasure
end AspisV8R19.SamplerObservedChallenge
