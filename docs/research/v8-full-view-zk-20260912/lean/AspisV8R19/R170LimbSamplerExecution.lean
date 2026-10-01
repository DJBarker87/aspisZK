import AspisV8R19.R169InnerSamplerExecution
import AspisV8R19.R137SamplerLimbLoop
import AspisV8R19.R137SamplerChallengeBridge

set_option autoImplicit false
namespace AspisV8R19.R170LimbSamplerExecution
open Aeneas Aeneas.Std Result ControlFlow
open AspisR156FullFreeze.aspis_core
open R167TranscriptPrimitiveExecution

abbrev Iter := core.slice.iter.IterMut U32

def quartic (x : AspisR137Transcript.field.QM31) : field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def outcome (x : core.result.Result AspisR137Transcript.field.QM31 Unit) :
    core.result.Result field.QM31 Unit :=
  match x with
  | .Ok x => .Ok (quartic x)
  | .Err e => .Err e

def finished (x : R137SamplerLimbLoop.Output) :
    transcript.Transcript × Option (core.result.Result field.QM31 Unit) × Iter :=
  (fromR137 x.1, x.2.1.map outcome, x.2.2)

theorem loop_map (n : Nat) (it : Iter) (back : Iter → Iter)
    (s : AspisR137Transcript.transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize)
    (hn : it.slice.len - it.i = n) :
    transcript.Transcript.challenge_qm31_loop0 it back (fromR137 s) b j = (do
      let v ← AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0 it back s b j
      ok (finished v)) := by
  induction n generalizing it back s b j with
  | zero =>
      have h : ¬ it.i < it.slice.len := by omega
      rw [transcript.Transcript.challenge_qm31_loop0, loop.eq_def]
      simp only [transcript.Transcript.challenge_qm31_loop0.body,
        core.slice.iter.IteratorIterMut.next, dif_neg h, bind_tc_ok]
      rw [AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0,
        loop.eq_def]
      simp only [R137SamplerLimbLoop.exhausted it back s b j h, bind_tc_ok]
      rfl
  | succ n ih =>
      have h : it.i < it.slice.len := by omega
      have hn' : it.slice.len - (it.i + 1) = n := by omega
      rw [transcript.Transcript.challenge_qm31_loop0, loop.eq_def]
      simp only [transcript.Transcript.challenge_qm31_loop0.body,
        core.slice.iter.IteratorIterMut.next, dif_pos h, bind_tc_ok,
        R169InnerSamplerExecution.eight_attempts_map]
      rw [AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0,
        loop.eq_def]
      simp only [AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0.body,
        core.slice.iter.IteratorIterMut.next, dif_pos h, bind_tc_ok]
      cases hs : AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0_loop0
        {start := 0#u32, «end» := AspisR137Transcript.transcript.CHALLENGE_RETRY_LIMIT}
        s b j (it.slice[it.i]) with
      | fail e => simp [hs]
      | div => simp [hs]
      | ok x =>
        rcases x with ⟨s1,b1,j1,v,accepted⟩
        cases accepted with
        | false => rfl
        | true =>
          simp only [bind_tc_ok, R169InnerSamplerExecution.finished, if_true]
          simpa only [transcript.Transcript.challenge_qm31_loop0,
            transcript.Transcript.challenge_qm31_loop0.body,
            AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0,
            AspisR137Transcript.transcript.Transcript.challenge_qm31_loop0.body,
            core.slice.iter.IteratorIterMut.next, bind_tc_ok]
            using ih {it with i := it.i + 1}
              (fun out => back {out with slice := out.slice.setAtNat it.i v}) s1 b1 j1 hn'

def returned (x : core.result.Result AspisR137Transcript.field.QM31 Unit ×
    AspisR137Transcript.transcript.Transcript) :
    core.result.Result field.QM31 Unit × transcript.Transcript :=
  (outcome x.1,fromR137 x.2)

theorem challenge_map (s : AspisR137Transcript.transcript.Transcript) :
    transcript.Transcript.challenge_qm31 (fromR137 s) = (do
      let v ← AspisR137Transcript.transcript.Transcript.challenge_qm31 s
      ok (returned v)) := by
  simp only [transcript.Transcript.challenge_qm31,
    AspisR137Transcript.transcript.Transcript.challenge_qm31,
    squeeze_map, to_from, bind_assoc_eq, lift, bind_tc_ok,
    field.M31.ZERO, AspisR137Transcript.field.M31.ZERO,
    Array.to_slice_mut, core.slice.Slice.iter_mut]
  cases hs : AspisR137Transcript.transcript.Transcript.squeeze_block s with
  | fail e => rfl
  | div => rfl
  | ok pair =>
    rcases pair with ⟨b,s1⟩
    simp only [bind_tc_ok]
    rw [loop_map 4 _ _ s1 b 0#usize (by rfl)]
    simp only [bind_assoc_eq, bind_tc_ok]
    congr 1
    funext x
    rcases x with ⟨s2,pending,it⟩
    simp only [finished]
    cases pending with
    | some r => rfl
    | none =>
      simp only [Option.map_none, returned, outcome, quartic, bind_assoc_eq]
      congr 1

def encodeResult (x : Option (List Nat)) : core.result.Result field.QM31 Unit :=
  outcome (R137SamplerChallengeBridge.encodeResult x)

theorem challenge_exact (H : DuplexFrames.Bytes → SourceDuplexStep.State)
    (s : SourceDuplexStep.State) :
    transcript.Transcript.challenge_qm31 (R167TranscriptPrimitiveExecution.transcriptFor H s) =
      .ok (encodeResult (QM31SamplerProgram.challengeRun H s).2.1,
        R167TranscriptPrimitiveExecution.transcriptFor H
          (QM31SamplerProgram.challengeRun H s).2.2) := by
  rw [R167TranscriptPrimitiveExecution.transcriptFor, challenge_map,
    R137SamplerChallengeBridge.challenge_exact]
  rfl

#print axioms challenge_exact
#print axioms challenge_map
#print axioms loop_map
end AspisV8R19.R170LimbSamplerExecution
