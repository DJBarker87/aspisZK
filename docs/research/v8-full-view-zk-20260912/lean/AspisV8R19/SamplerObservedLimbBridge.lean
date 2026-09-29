import AspisV8R19.SamplerObservedInnerLoop
import AspisV8R19.SamplerLimbBridge

/-! Actual instrumented per-limb observations equal the retained causal
oracle program's trace, under the explicit deterministic adapter. The raw
observer history is retained as a witness, rather than inferred from values. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedLimbBridge
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerObservation SamplerObservedLaws SamplerObservedInnerLoop
open SamplerLimbBridge SqueezeOracleBridge SamplerObservedSqueeze
open SourceDuplexStep DuplexFrames

theorem draw_trace (H : Bytes → State) (c : QM31SamplerProgram.Cursor) (history : Trace) :
    ∃ observed, draw (encodeCursor H c) history =
      .ok ((encodeCursor H (QM31SamplerProgram.readRun H c).2.2,
        encodeWord (QM31SamplerProgram.readRun H c).2.1),observed) ∧
      decodeTrace observed=decodeTrace history++(QM31SamplerProgram.readRun H c).1 := by
  by_cases h : c.index.val=8
  · have hn : ¬ c.index.val<8 := by omega
    refine ⟨history++rawCalls H c.state,?_,?_⟩
    · simp only [draw,encodeCursor,dif_neg hn,bind_apply,pure_apply,
        adapter_execution,bind_tc_ok,QM31SamplerProgram.readRun,dif_pos h]
      have hw := source_word_encoded (step H c.state).1 0
      simpa [encodeCursor] using congrArg (fun word => Result.ok
        ((encodeCursor H ⟨(step H c.state).2,(step H c.state).1,1⟩,word),
          history++rawCalls H c.state)) hw
    · simp only [decode_append,raw_calls_decode,QM31SamplerProgram.readRun,dif_pos h]
  · have hn : c.index.val<8 := by have := c.index.isLt; omega
    refine ⟨history,?_,?_⟩
    · simp only [draw,encodeCursor,dif_pos hn,pure_apply,QM31SamplerProgram.readRun,dif_neg h]
      have hw := source_word_encoded c.block ⟨c.index.val,hn⟩
      exact congrArg (fun word => Result.ok
        ((encodeCursor H ⟨c.state,c.block,⟨c.index.val+1,by omega⟩⟩,word),history)) hw
    · simp only [QM31SamplerProgram.readRun,dif_neg h,List.append_nil]

theorem limb_trace (H : Bytes → State) (n : Nat) (c : QM31SamplerProgram.Cursor)
    (old : field.M31) (history : Trace) :
    ∃ observed, bounded n (encodeCursor H c) old history =
      .ok (encodeFinished H (QM31SamplerProgram.limbRun H n c).2 old,observed) ∧
      decodeTrace observed=decodeTrace history++(QM31SamplerProgram.limbRun H n c).1 := by
  induction n generalizing c history with
  | zero => exact ⟨history,rfl,(by simp [QM31SamplerProgram.limbRun])⟩
  | succ n ih =>
      obtain ⟨t,hd,ht⟩ := draw_trace H c history
      have hb := read_bound H c
      by_cases hm : SamplerWords.masked 31 (QM31SamplerProgram.readRun H c).2.1=2147483647
      · have hw : encodeWord (QM31SamplerProgram.readRun H c).2.1 &&& field.P=field.P := by
          apply UScalar.eq_of_val_eq
          rw [mask_value _ hb,hm]
          simp only [field.P]
          rfl
        obtain ⟨t1,he,ht1⟩ := ih (QM31SamplerProgram.readRun H c).2.2 t
        refine ⟨t1,?_,?_⟩
        · simpa only [bounded,bind_apply,hd,bind_tc_ok,hw,bne_self_eq_false,
            Bool.false_eq_true,if_false,QM31SamplerProgram.limbRun,hm,if_true] using he
        · simpa only [ht,List.append_assoc,QM31SamplerProgram.limbRun,hm,if_true] using ht1
      · have hw : encodeWord (QM31SamplerProgram.readRun H c).2.1 &&& field.P≠field.P := by
          intro he
          have hv := congrArg UScalar.val he
          rw [mask_value _ hb] at hv
          apply hm
          simpa [field.P] using hv
        have htrue : (encodeWord (QM31SamplerProgram.readRun H c).2.1 &&& field.P != field.P)=true :=
          bne_iff_ne.mpr hw
        refine ⟨t,?_,?_⟩
        · simp only [bounded,bind_apply,hd,bind_tc_ok,htrue,if_true,pure_apply,
            QM31SamplerProgram.limbRun,hm,if_false,encodeFinished,Option.isSome_some]
          rw [mask_encoded _ hb]
        · simpa only [QM31SamplerProgram.limbRun,hm,if_false] using ht

theorem instrumented_limb_trace (H : Bytes → State) (c : QM31SamplerProgram.Cursor)
    (old : field.M31) (history : Trace) :
    ∃ observed, SamplerObservedSource.challenge_qm31_loop0_loop0
      {start:=0#u32, «end»:=transcript.CHALLENGE_RETRY_LIMIT}
      (transcriptFor H c.state) (encodeState c.block)
      (SamplerInnerLoop.index (encodeCursor H c)) old history =
      .ok (encodeFinished H (QM31SamplerProgram.limbRun H 8 c).2 old,observed) ∧
      decodeTrace observed=decodeTrace history++(QM31SamplerProgram.limbRun H 8 c).1 := by
  change ∃ observed, SamplerObservedSource.challenge_qm31_loop0_loop0 _
    (encodeCursor H c).state (encodeCursor H c).block _ old history = _ ∧ _
  simp only [eight_attempts]
  exact limb_trace H 8 c old history

theorem decoded_limb_trace (H : Bytes → State) (c : QM31SamplerProgram.Cursor)
    (old : field.M31) (history : Trace) :
    (do let (out,observed) ← SamplerObservedSource.challenge_qm31_loop0_loop0
          {start:=0#u32, «end»:=transcript.CHALLENGE_RETRY_LIMIT}
          (transcriptFor H c.state) (encodeState c.block)
          (SamplerInnerLoop.index (encodeCursor H c)) old history
        ok (out,decodeTrace observed)) =
      .ok (encodeFinished H (QM31SamplerProgram.limbRun H 8 c).2 old,
        decodeTrace history++(QM31SamplerProgram.limbRun H 8 c).1) := by
  obtain ⟨t,he,ht⟩ := instrumented_limb_trace H c old history
  rw [he]
  simp only [bind_tc_ok,ht]

theorem instrumented_limb_erasure (H : Bytes → State) (c : QM31SamplerProgram.Cursor)
    (old : field.M31) (history : Trace) :
    (do let (out,_) ← SamplerObservedSource.challenge_qm31_loop0_loop0
          {start:=0#u32, «end»:=transcript.CHALLENGE_RETRY_LIMIT}
          (transcriptFor H c.state) (encodeState c.block)
          (SamplerInnerLoop.index (encodeCursor H c)) old history
        ok out) =
      transcript.Transcript.challenge_qm31_loop0_loop0
        {start:=0#u32, «end»:=transcript.CHALLENGE_RETRY_LIMIT}
        (transcriptFor H c.state) (encodeState c.block)
        (SamplerInnerLoop.index (encodeCursor H c)) old := by
  obtain ⟨t,he,_⟩ := instrumented_limb_trace H c old history
  rw [he,SamplerLimbBridge.source_limb_exact]
  rfl

#print axioms draw_trace
#print axioms limb_trace
#print axioms instrumented_limb_trace
#print axioms decoded_limb_trace
#print axioms instrumented_limb_erasure
end AspisV8R19.SamplerObservedLimbBridge
