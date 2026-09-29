import AspisV8R19.SamplerWordBridge
import AspisV8R19.SamplerInnerLoop
import AspisV8R19.QM31SamplerProgram

/-! Exact word/cursor and per-limb value correspondence under the explicit
total deterministic hash adapter. Not concrete SHA ideality or a trace law. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerLimbBridge
open Aeneas Aeneas.Std Result AspisR72Sampler SqueezeOracleBridge SamplerWordBridge
open SourceDuplexStep DuplexFrames

def encodeWord (n : Nat) : U32 := UScalar.ofNatCore (n % 4294967296) (Nat.mod_lt _ (by decide))
theorem word_value (n : Nat) (h : n < 4294967296) : (encodeWord n).val = n :=
  Nat.mod_eq_of_lt h

def encodeCursor (H : Bytes → State) (c : QM31SamplerProgram.Cursor) : SamplerInnerLoop.Cursor :=
  ⟨transcriptFor H c.state,encodeState c.block,c.index⟩

theorem source_word_encoded (s : State) (j : Fin 8) :
    core.num.U32.from_le_bytes (SamplerWordRead.four (encodeState s) (j.val*4) (by omega)) =
      encodeWord (SamplerWords.word s j) := by
  apply UScalar.eq_of_val_eq
  rw [word_value _ (SamplerWords.word_bound s j)]
  simpa only [Nat.mul_comm] using source_word s j

theorem read_bound (H : Bytes → State) (c : QM31SamplerProgram.Cursor) :
    (QM31SamplerProgram.readRun H c).2.1 < 4294967296 := by
  unfold QM31SamplerProgram.readRun
  split <;> exact SamplerWords.word_bound _ _

theorem draw_exact (H : Bytes → State) (c : QM31SamplerProgram.Cursor) :
    SamplerInnerLoop.draw (encodeCursor H c) =
      .ok (encodeCursor H (QM31SamplerProgram.readRun H c).2.2,
        encodeWord (QM31SamplerProgram.readRun H c).2.1) := by
  by_cases h : c.index.val=8
  · have hn : ¬ c.index.val<8 := by omega
    simp only [SamplerInnerLoop.draw,encodeCursor,dif_neg hn,
      SqueezeOracleBridge.source_step,bind_tc_ok,QM31SamplerProgram.readRun,dif_pos h]
    have hw := source_word_encoded (step H c.state).1 0
    simpa [encodeCursor] using congrArg
      (fun word => Result.ok (encodeCursor H ⟨(step H c.state).2,(step H c.state).1,1⟩,word)) hw
  · have hn : c.index.val<8 := by have := c.index.isLt; omega
    simp only [SamplerInnerLoop.draw,encodeCursor,dif_pos hn,QM31SamplerProgram.readRun,dif_neg h]
    have hw := source_word_encoded c.block ⟨c.index.val,hn⟩
    exact congrArg (fun word => Result.ok
      (encodeCursor H ⟨c.state,c.block,⟨c.index.val+1,by omega⟩⟩,word)) hw

theorem mask_value (n : Nat) (h : n < 4294967296) :
    (encodeWord n &&& field.P).val = SamplerWords.masked 31 n := by
  rw [source_mask,word_value n h]

theorem mask_encoded (n : Nat) (h : n < 4294967296) :
    encodeWord n &&& field.P = encodeWord (SamplerWords.masked 31 n) := by
  apply UScalar.eq_of_val_eq
  rw [mask_value n h,word_value]
  have hb := SamplerWords.masked_bound 31 n
  change SamplerWords.masked 31 n < 2147483648 at hb
  omega

def encodeFinished (H : Bytes → State) (r : Option Nat × QM31SamplerProgram.Cursor)
    (old : field.M31) : SamplerInnerStep.Finished :=
  let c := encodeCursor H r.2
  (c.state,c.block,SamplerInnerLoop.index c,
    match r.1 with | none => old | some a => encodeWord a,
    r.1.isSome)

theorem limb_exact (H : Bytes → State) (n : Nat) (c : QM31SamplerProgram.Cursor)
    (old : field.M31) :
    SamplerInnerLoop.bounded n (encodeCursor H c) old =
      .ok (encodeFinished H (QM31SamplerProgram.limbRun H n c).2 old) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
      have hb := read_bound H c
      by_cases hm : SamplerWords.masked 31 (QM31SamplerProgram.readRun H c).2.1=2147483647
      · have hw : encodeWord (QM31SamplerProgram.readRun H c).2.1 &&& field.P=field.P := by
          apply UScalar.eq_of_val_eq
          rw [mask_value _ hb,hm]
          simp only [field.P]
          rfl
        simp only [SamplerInnerLoop.bounded,draw_exact,bind_tc_ok,hw,bne_self_eq_false,
          Bool.false_eq_true,if_false,QM31SamplerProgram.limbRun,hm,if_true]
        exact ih _
      · have hw : encodeWord (QM31SamplerProgram.readRun H c).2.1 &&& field.P≠field.P := by
          intro he
          have hv := congrArg UScalar.val he
          rw [mask_value _ hb] at hv
          apply hm
          simpa [field.P] using hv
        have ht : (encodeWord (QM31SamplerProgram.readRun H c).2.1 &&& field.P != field.P)=true :=
          bne_iff_ne.mpr hw
        simp only [SamplerInnerLoop.bounded,draw_exact,bind_tc_ok,ht,if_true,
          QM31SamplerProgram.limbRun,hm,if_false,encodeFinished,Option.isSome_some]
        rw [mask_encoded _ hb]

theorem source_limb_exact (H : Bytes → State) (c : QM31SamplerProgram.Cursor)
    (old : field.M31) :
    transcript.Transcript.challenge_qm31_loop0_loop0
      {start:=0#u32, «end»:=transcript.CHALLENGE_RETRY_LIMIT}
      (transcriptFor H c.state) (encodeState c.block)
      (SamplerInnerLoop.index (encodeCursor H c)) old =
      .ok (encodeFinished H (QM31SamplerProgram.limbRun H 8 c).2 old) := by
  change transcript.Transcript.challenge_qm31_loop0_loop0 _
    (encodeCursor H c).state (encodeCursor H c).block _ old = _
  rw [SamplerInnerLoop.eight_attempts,limb_exact]

#print axioms word_value
#print axioms source_word_encoded
#print axioms read_bound
#print axioms draw_exact
#print axioms mask_value
#print axioms mask_encoded
#print axioms limb_exact
#print axioms source_limb_exact
end AspisV8R19.SamplerLimbBridge
