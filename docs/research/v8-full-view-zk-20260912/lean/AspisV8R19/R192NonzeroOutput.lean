import AspisV8R19.R176CallbackSamplerExecution
import AspisV8R19.R177CircleScheduleBridge

set_option autoImplicit false
namespace AspisV8R19.R192NonzeroOutput
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze AspisR156FullFreeze.aspis_core
open DuplexFrames SourceDuplexStep
open R170LimbSamplerExecution (quartic outcome)

 theorem canonical_words (a b c d : Nat)
    (ha : a < 2147483647) (hb : b < 2147483647)
    (hc : c < 2147483647) (hd : d < 2147483647) :
    R165QuarticExecution.Canonical
      (quartic (R139NonzeroModelBridge.encodeQM31 a b c d)) := by
  rw [R177CircleScheduleBridge.quartic_adapter]
  change (SamplerLimbBridge.encodeWord a).val < 2147483647 ∧
    (SamplerLimbBridge.encodeWord b).val < 2147483647 ∧
    (SamplerLimbBridge.encodeWord c).val < 2147483647 ∧
    (SamplerLimbBridge.encodeWord d).val < 2147483647
  simpa only [SamplerLimbBridge.word_value a (by omega),
    SamplerLimbBridge.word_value b (by omega),
    SamplerLimbBridge.word_value c (by omega),
    SamplerLimbBridge.word_value d (by omega)] using ⟨ha, hb, hc, hd⟩

 theorem successful_nonzero (H : Bytes → State) (s : State)
    (q : field.QM31) (next : transcript.Transcript)
    (h : transcript.Transcript.challenge_nonzero_qm31
      (R167TranscriptPrimitiveExecution.transcriptFor H s) = .ok (.Ok q, next)) :
    R165QuarticExecution.Canonical q ∧ R165QuarticExecution.decode q ≠ 0 := by
  rw [R173NonzeroExecution.challenge_exact] at h
  cases hr : (SamplerWrapperPolicies.nonzeroRun H s).2.1 with
  | error e => simp [hr, R139NonzeroModelBridge.encodePolicyResult, outcome] at h
  | ok xs =>
      obtain ⟨hlen, hcan, _⟩ := SamplerWrapperPolicies.nonzero_result H s xs hr
      have hnz := SamplerFieldDecode.nonzero_field_result H s xs hr
      obtain ⟨a,b,c,d,hxs⟩ : ∃ a b c d, xs = [a,b,c,d] :=
        ⟨_,_,_,_,List.eq_getElem_of_length_eq_four xs hlen⟩
      subst xs
      have ha : a < 2147483647 := hcan a (by simp)
      have hb : b < 2147483647 := hcan b (by simp)
      have hc : c < 2147483647 := hcan c (by simp)
      have hd : d < 2147483647 := hcan d (by simp)
      have hq : quartic (R139NonzeroModelBridge.encodeQM31 a b c d) = q := by
        simpa only [hr, R139NonzeroModelBridge.encodePolicyResult, outcome,
          core.result.Result.Ok.injEq] using
          congrArg Prod.fst (Result.ok.inj h)
      subst q
      refine ⟨canonical_words a b c d ha hb hc hd, ?_⟩
      rw [R177CircleScheduleBridge.decode_words a b c d ha hb hc hd]
      exact hnz

 theorem callback_successful_nonzero (H : Bytes → State) (s : State)
    (q : field.QM31) (next : transcript.Transcript)
    (h : sample (R167TranscriptPrimitiveExecution.transcriptFor H s) true =
      .ok (.Ok q, next)) :
    R165QuarticExecution.Canonical q ∧ R165QuarticExecution.decode q ≠ 0 := by
  rw [R176CallbackSamplerExecution.sample_factored] at h
  simp only [R176CallbackSamplerExecution.chosen, if_true] at h
  cases hs : transcript.Transcript.challenge_nonzero_qm31
      (R167TranscriptPrimitiveExecution.transcriptFor H s) with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok pair =>
      rcases pair with ⟨r, st⟩
      cases r with
      | Err e => simp [hs, R176CallbackSamplerExecution.callbackOutcome] at h
      | Ok value =>
          simp only [hs, bind_tc_ok, R176CallbackSamplerExecution.callbackOutcome] at h
          have hq : value = q :=
            core.result.Result.Ok.inj (congrArg Prod.fst (Result.ok.inj h))
          subst q
          exact successful_nonzero H s value st hs

#print axioms canonical_words
#print axioms successful_nonzero
#print axioms callback_successful_nonzero
end AspisV8R19.R192NonzeroOutput
