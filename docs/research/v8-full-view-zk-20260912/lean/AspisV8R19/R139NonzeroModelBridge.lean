import AspisV8R19.R139SamplerSourceBridge
import AspisV8R19.SamplerWrapperPolicies

/-! Value-level bridge between the exact R137 nonzero test and the existing
source-shaped nonzero policy model. -/
set_option autoImplicit false
namespace AspisV8R19.R139NonzeroModelBridge

open Aeneas Aeneas.Std Result AspisR137Transcript
open DuplexFrames SourceDuplexStep
open R137SamplerLimbBridge R137SamplerChallengeBridge

def encodeQM31 (a b c d : Nat) : field.QM31 :=
  {c0:={a:=encodeWord a,b:=encodeWord b},
   c1:={a:=encodeWord c,b:=encodeWord d}}

theorem encodeWord_eq_zero_iff (n : Nat) (hn : n < 4294967296) :
    encodeWord n = 0#u32 ↔ n = 0 := by
  constructor
  · intro h
    have hv := congrArg UScalar.val h
    rw [word_value n hn] at hv
    exact hv
  · intro h
    subst n
    apply UScalar.eq_of_val_eq
    rfl

theorem encodeQM31_eq_zero_iff (a b c d : Nat)
    (ha : a < 4294967296) (hb : b < 4294967296)
    (hc : c < 4294967296) (hd : d < 4294967296) :
    encodeQM31 a b c d = field.QM31.ZERO ↔
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun q : field.QM31 => q.c0.a) h
    have h1 := congrArg (fun q : field.QM31 => q.c0.b) h
    have h2 := congrArg (fun q : field.QM31 => q.c1.a) h
    have h3 := congrArg (fun q : field.QM31 => q.c1.b) h
    simp only [encodeQM31, field.QM31.ZERO] at h0 h1 h2 h3
    exact ⟨(encodeWord_eq_zero_iff a ha).mp h0,
      (encodeWord_eq_zero_iff b hb).mp h1,
      (encodeWord_eq_zero_iff c hc).mp h2,
      (encodeWord_eq_zero_iff d hd).mp h3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [encodeQM31, encodeWord, field.QM31.ZERO]

theorem generated_ne_zero_false (a b c d : Nat)
    (hz : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) :
    core.cmp.PartialEq.ne.trait_default
        field.QM31.Insts.CoreCmpPartialEqQM31
        (encodeQM31 a b c d) field.QM31.ZERO = .ok false := by
  rcases hz with ⟨rfl, rfl, rfl, rfl⟩
  simp [core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    field.M31.Insts.CoreCmpPartialEqM31.eq,
    encodeQM31, encodeWord, field.QM31.ZERO]

theorem generated_ne_zero_true (a b c d : Nat)
    (ha : a < 4294967296) (hb : b < 4294967296)
    (hc : c < 4294967296) (hd : d < 4294967296)
    (hz : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    core.cmp.PartialEq.ne.trait_default
        field.QM31.Insts.CoreCmpPartialEqQM31
        (encodeQM31 a b c d) field.QM31.ZERO = .ok true := by
  simp only [core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    field.M31.Insts.CoreCmpPartialEqM31.eq,
    bind_tc_ok, field.QM31.ZERO, encodeQM31]
  simp only [encodeWord_eq_zero_iff a ha, encodeWord_eq_zero_iff b hb,
    encodeWord_eq_zero_iff c hc, encodeWord_eq_zero_iff d hd]
  by_cases h0 : a = 0 <;> by_cases h1 : b = 0 <;>
    by_cases h2 : c = 0 <;> by_cases h3 : d = 0 <;>
    simp [h0, h1, h2, h3] at hz ⊢

def encodePolicyResult :
    Except SamplerWrapperPolicies.Error (List Nat) →
      core.result.Result field.QM31 transcript.ChallengeSampleExhausted
  | .error _ => .Err ()
  | .ok [a, b, c, d] => .Ok (encodeQM31 a b c d)
  | .ok _ => .Err ()

theorem encodeResult_none : encodeResult none = .Err () := rfl

theorem encodeResult_four (a b c d : Nat) :
    encodeResult (some [a, b, c, d]) =
      .Ok (encodeQM31 a b c d) := rfl

theorem bounded_model_exact (H : Bytes → State) (n : Nat) (s : State) :
    R137NonzeroLoop.bounded n
        (R137TranscriptPrimitiveBridge.transcriptFor H s) =
      .ok (encodePolicyResult
          (BoundedSamplerWrapper.run SamplerWrapperPolicies.nonzeroAccept
            SamplerWrapperPolicies.Error.challengeExhausted
            SamplerWrapperPolicies.Error.challengeExhausted H n s).2.1,
        R137TranscriptPrimitiveBridge.transcriptFor H
          (BoundedSamplerWrapper.run SamplerWrapperPolicies.nonzeroAccept
            SamplerWrapperPolicies.Error.challengeExhausted
            SamplerWrapperPolicies.Error.challengeExhausted H n s).2.2) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [R137NonzeroLoop.bounded,
        R137SamplerChallengeBridge.challenge_exact]
      simp only [bind_tc_ok]
      cases hx : (QM31SamplerProgram.challengeRun H s).2.1 with
      | none =>
          rw [encodeResult_none]
          simp [BoundedSamplerWrapper.run, hx, encodePolicyResult]
      | some values =>
          obtain ⟨hlen, hcan⟩ :=
            QM31SamplerInvariants.challenge_four_canonical_limbs H s
              values hx
          obtain ⟨a, b, c, d, hv⟩ :
              ∃ a b c d, values = [a, b, c, d] :=
            ⟨_, _, _, _, List.eq_getElem_of_length_eq_four values hlen⟩
          subst values
          have ha : a < 4294967296 := by
            have := hcan a (by simp)
            omega
          have hb : b < 4294967296 := by
            have := hcan b (by simp)
            omega
          have hc : c < 4294967296 := by
            have := hcan c (by simp)
            omega
          have hd : d < 4294967296 := by
            have := hcan d (by simp)
            omega
          rw [encodeResult_four]
          simp only
          by_cases hz : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0
          · rw [generated_ne_zero_false a b c d hz]
            simp only [bind_tc_ok, Bool.false_eq_true, if_false]
            have hi := ih (QM31SamplerProgram.challengeRun H s).2.2
            simpa [BoundedSamplerWrapper.run, hx,
              SamplerWrapperPolicies.nonzeroAccept, hz, encodePolicyResult]
              using hi
          · rw [generated_ne_zero_true a b c d ha hb hc hd hz]
            simp [BoundedSamplerWrapper.run, hx,
              SamplerWrapperPolicies.nonzeroAccept, hz, encodePolicyResult,
              encodeQM31]

theorem nonzero_source_model_exact (H : Bytes → State) (s : State) :
    transcript.Transcript.challenge_nonzero_qm31
        (R137TranscriptPrimitiveBridge.transcriptFor H s) =
      .ok (encodePolicyResult (SamplerWrapperPolicies.nonzeroRun H s).2.1,
        R137TranscriptPrimitiveBridge.transcriptFor H
          (SamplerWrapperPolicies.nonzeroRun H s).2.2) := by
  rw [R137NonzeroLoop.entry_three]
  exact bounded_model_exact H 3 s

#print axioms encodeWord_eq_zero_iff
#print axioms encodeQM31_eq_zero_iff
#print axioms generated_ne_zero_false
#print axioms generated_ne_zero_true
#print axioms encodeResult_none
#print axioms encodeResult_four
#print axioms bounded_model_exact
#print axioms nonzero_source_model_exact

end AspisV8R19.R139NonzeroModelBridge
