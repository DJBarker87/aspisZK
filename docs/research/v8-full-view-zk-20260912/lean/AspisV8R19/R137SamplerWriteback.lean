import AspisV8R19.R137SamplerLimbBridge
import AspisV8R19.R137SamplerLimbLoop
import AspisV8R19.QM31SamplerInvariants

/-! Exact correspondence for the R137 sampler's deferred mutable limb
write-back. -/
set_option autoImplicit false
namespace AspisV8R19.R137SamplerWriteback

open Aeneas Aeneas.Std Result AspisR137Transcript
open R137SamplerLimbBridge R137SamplerLimbLoop
open SourceDuplexStep DuplexFrames

def writeValues : Iter → List Nat → Iter
  | it, [] => it
  | it, v :: vs =>
      store (writeValues { it with i := it.i + 1 } vs) it.i (encodeWord v)

def Matches (H : Bytes → State) (result : Result Output)
    (model : Option (List Nat) × QM31SamplerProgram.Cursor)
    (it : Iter) (back : Iter → Iter) : Prop :=
  match model.1 with
  | none => ∃ out, result = .ok
      (R137TranscriptPrimitiveBridge.transcriptFor H model.2.state,
        some (.Err ()), out)
  | some values => result = .ok
      (R137TranscriptPrimitiveBridge.transcriptFor H model.2.state,
        none, back (writeValues it values))

theorem bounded_matches (H : Bytes → State) (n : Nat)
    (c : QM31SamplerProgram.Cursor) (it : Iter) (back : Iter → Iter)
    (hn : it.slice.len - it.i = n) :
    Matches H
      (bounded n it back
        (R137TranscriptPrimitiveBridge.transcriptFor H c.state)
        (SqueezeOracleBridge.encodeState c.block)
        (R137SamplerInnerLoop.index (encodeCursor H c)))
      (QM31SamplerProgram.limbsRun H n c).2 it back := by
  induction n generalizing c it back with
  | zero => rfl
  | succ n ih =>
      have hi : it.i < it.slice.len := by omega
      have hn' : it.slice.len - (it.i + 1) = n := by omega
      simp only [bounded, dif_pos hi, source_limb_exact,
        QM31SamplerProgram.limbsRun]
      cases hx : (QM31SamplerProgram.limbRun H 8 c).2.1 with
      | none =>
          simp only [encodeFinished, hx, Option.isSome_none, encodeCursor,
            bind_tc_ok, Bool.false_eq_true, if_false, Matches]
          exact ⟨_, rfl⟩
      | some a =>
          simp only [encodeFinished, hx, Option.isSome_some, encodeCursor,
            bind_tc_ok, if_true]
          have ht := ih (QM31SamplerProgram.limbRun H 8 c).2.2
            { it with i := it.i + 1 }
            (fun out => back (store out it.i (encodeWord a))) hn'
          cases hy : (QM31SamplerProgram.limbsRun H n
            (QM31SamplerProgram.limbRun H 8 c).2.2).2.1 with
          | none =>
              simpa only [Matches, hy, Option.map_none, encodeCursor] using ht
          | some vs =>
              simpa only [Matches, hy, Option.map_some, writeValues,
                encodeCursor] using ht

theorem written_four (a b c d : Nat) :
    (writeValues initialIter [a, b, c, d]).slice.val =
      [encodeWord a, encodeWord b, encodeWord c, encodeWord d] := by
  simp [writeValues, store, initialIter, initial, Array.repeat,
    Array.to_slice, Slice.setAtNat]

theorem finish_four (s : transcript.Transcript) (a b c d : Nat) :
    finish (s, none, writeValues initialIter [a, b, c, d]) =
      .ok (.Ok {c0:={a:=encodeWord a,b:=encodeWord b},c1:={a:=encodeWord c,b:=encodeWord d}},s) := by
  simp [finish, Array.from_slice, written_four, Array.index_usize]

#print axioms bounded_matches
#print axioms written_four
#print axioms finish_four

end AspisV8R19.R137SamplerWriteback
