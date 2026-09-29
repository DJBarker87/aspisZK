import AspisV8R19.SamplerWriteback

/-! Complete generated QM31 challenge value/state correspondence under the
explicit deterministic hash adapter. Oracle traces remain a separate claim. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerChallengeBridge
open Aeneas Aeneas.Std Result AspisR72Sampler SamplerLimbBridge SamplerLimbLoop SamplerWriteback
open SourceDuplexStep DuplexFrames SqueezeOracleBridge

def encodeResult : Option (List Nat) → core.result.Result field.QM31 transcript.ChallengeSampleExhausted
  | some [a,b,c,d] => .Ok { c0 := { a := encodeWord a, b := encodeWord b }, c1 := { a := encodeWord c, b := encodeWord d } }
  | _ => .Err ()

theorem finish_model (H : Bytes → State) (c : QM31SamplerProgram.Cursor) :
    (do
      let out ← bounded 4 initialIter (fun it => it) (transcriptFor H c.state)
        (encodeState c.block) (SamplerInnerLoop.index (encodeCursor H c))
      finish out) =
      .ok (encodeResult (QM31SamplerProgram.limbsRun H 4 c).2.1,
        transcriptFor H (QM31SamplerProgram.limbsRun H 4 c).2.2.state) := by
  have hm := bounded_matches H 4 c initialIter (fun it => it) (by rfl)
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
      simp only [bind_tc_ok,finish_four,encodeResult]

theorem challenge_exact (H : Bytes → State) (s : State) :
    transcript.Transcript.challenge_qm31 (transcriptFor H s) =
      .ok (encodeResult (QM31SamplerProgram.challengeRun H s).2.1,
        transcriptFor H (QM31SamplerProgram.challengeRun H s).2.2) := by
  rw [entry_four,source_step]
  simp only [bind_tc_ok]
  have hm := finish_model H ⟨(step H s).2,(step H s).1,0⟩
  have hi : SamplerInnerLoop.index (encodeCursor H ⟨(step H s).2,(step H s).1,0⟩)=0#usize := by
    apply UScalar.eq_of_val_eq
    rfl
  rw [hi] at hm
  simpa only [QM31SamplerProgram.challengeRun] using hm

theorem challenge_exhaustion (H : Bytes → State) (s : State)
    (h : (QM31SamplerProgram.challengeRun H s).2.1=none) :
    transcript.Transcript.challenge_qm31 (transcriptFor H s) =
      .ok (.Err (),transcriptFor H (QM31SamplerProgram.challengeRun H s).2.2) := by
  rw [challenge_exact,h]; rfl

theorem challenge_success (H : Bytes → State) (s : State) (a b c d : Nat)
    (h : (QM31SamplerProgram.challengeRun H s).2.1=some [a,b,c,d]) :
    transcript.Transcript.challenge_qm31 (transcriptFor H s) =
      .ok (.Ok { c0 := { a := encodeWord a, b := encodeWord b }, c1 := { a := encodeWord c, b := encodeWord d } },
        transcriptFor H (QM31SamplerProgram.challengeRun H s).2.2) := by
  rw [challenge_exact,h]; rfl

theorem successful_value_canonical (H : Bytes → State) (s : State)
    (q : field.QM31) (next : transcript.Transcript)
    (h : transcript.Transcript.challenge_qm31 (transcriptFor H s)=.ok (.Ok q,next)) :
    q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
      q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647 := by
  cases hm : (QM31SamplerProgram.challengeRun H s).2.1 with
  | none =>
      have he := h.symm.trans (challenge_exhaustion H s hm)
      cases he
  | some values =>
      obtain ⟨hlen,hcan⟩ := QM31SamplerInvariants.challenge_four_canonical_limbs H s values hm
      obtain ⟨a,b,c,d,hv⟩ : ∃ a b c d, values=[a,b,c,d] :=
        ⟨_,_,_,_,List.eq_getElem_of_length_eq_four values hlen⟩
      subst values
      have he := Result.ok.inj (h.symm.trans (challenge_success H s a b c d hm))
      have hq := core.result.Result.Ok.inj (congrArg Prod.fst he)
      subst q
      have ha := hcan a (by simp)
      have hb := hcan b (by simp)
      have hc := hcan c (by simp)
      have hd := hcan d (by simp)
      simpa only [word_value a (by omega),word_value b (by omega),
        word_value c (by omega),word_value d (by omega)] using And.intro ha (And.intro hb (And.intro hc hd))

#print axioms finish_model
#print axioms challenge_exact
#print axioms challenge_exhaustion
#print axioms challenge_success
#print axioms successful_value_canonical
end AspisV8R19.SamplerChallengeBridge
