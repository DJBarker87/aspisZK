import AspisV8R19.SamplerObservedLimbLoop
import AspisV8R19.SamplerWriteback

/-! Deferred writes plus observed history, including early limb exhaustion.
No trace is reconstructed from equality of the final value. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedWriteback
open Aeneas Aeneas.Std Result AspisR72Sampler
open SamplerLimbBridge SamplerLimbLoop
open SamplerWriteback (writeValues)
open SamplerObservation SamplerObservedLaws SamplerObservedLimbBridge
open SourceDuplexStep DuplexFrames SqueezeOracleBridge

def Matches (H : Bytes → State) (result : Result (Output × Trace))
    (model : Option (List Nat) × QM31SamplerProgram.Cursor) (it : Iter)
    (back : Iter → Iter) (observed : Trace) : Prop :=
  match model.1 with
  | none => ∃ out, result = .ok ((transcriptFor H model.2.state,some (.Err ()),out),observed)
  | some values => result = .ok
      ((transcriptFor H model.2.state,none,back (writeValues it values)),observed)

theorem bounded_matches (H : Bytes → State) (n : Nat) (c : QM31SamplerProgram.Cursor)
    (it : Iter) (back : Iter → Iter) (hn : it.slice.len-it.i=n) (history : Trace) :
    ∃ observed, Matches H (SamplerObservedLimbLoop.bounded n it back (transcriptFor H c.state)
      (encodeState c.block) (SamplerInnerLoop.index (encodeCursor H c)) history)
      (QM31SamplerProgram.limbsRun H n c).2 it back observed ∧
      decodeTrace observed=decodeTrace history++(QM31SamplerProgram.limbsRun H n c).1 := by
  induction n generalizing c it back history with
  | zero => exact ⟨history,rfl,(by simp [QM31SamplerProgram.limbsRun])⟩
  | succ n ih =>
      have hi : it.i < it.slice.len := by omega
      have hn' : it.slice.len-(it.i+1)=n := by omega
      obtain ⟨t,he,ht⟩ := instrumented_limb_trace H c (it.slice[it.i]) history
      cases hx : (QM31SamplerProgram.limbRun H 8 c).2.1 with
      | none =>
          refine ⟨t,?_,?_⟩
          · simp only [SamplerObservedLimbLoop.bounded,dif_pos hi,bind_apply]
            erw [he]
            simp only [bind_tc_ok,
              encodeFinished,Option.isSome_none,encodeCursor,Bool.false_eq_true,if_false,
              pure_apply,QM31SamplerProgram.limbsRun,hx,Matches]
            exact ⟨_,rfl⟩
          · simpa only [QM31SamplerProgram.limbsRun,hx] using ht
      | some a =>
          obtain ⟨t1,hm,ht1⟩ := ih (QM31SamplerProgram.limbRun H 8 c).2.2
            {it with i:=it.i+1} (fun out => back (store out it.i (encodeWord a))) hn' t
          refine ⟨t1,?_,?_⟩
          · simp only [SamplerObservedLimbLoop.bounded,dif_pos hi,bind_apply]
            erw [he]
            simp only [bind_tc_ok,
              encodeFinished,Option.isSome_some,encodeCursor,if_true,QM31SamplerProgram.limbsRun,hx]
            cases hy : (QM31SamplerProgram.limbsRun H n (QM31SamplerProgram.limbRun H 8 c).2.2).2.1 with
            | none => simpa only [Matches,hy,Option.map_none,encodeCursor] using hm
            | some vs => simpa only [Matches,hy,Option.map_some,writeValues,encodeCursor] using hm
          · simpa only [ht,List.append_assoc,QM31SamplerProgram.limbsRun,hx] using ht1

#print axioms bounded_matches
end AspisV8R19.SamplerObservedWriteback
