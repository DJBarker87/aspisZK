import AspisV8R19.R137SamplerInnerLoop

/-! Finite execution of the exact R137 mutable four-limb loop, retaining the
source's deferred write-back functions. -/
set_option autoImplicit false
namespace AspisV8R19.R137SamplerLimbLoop

open Aeneas Aeneas.Std Result ControlFlow AspisR137Transcript

abbrev Iter := core.slice.iter.IterMut field.M31
abbrev Output := transcript.Transcript ×
  Option (core.result.Result field.QM31
    transcript.ChallengeSampleExhausted) × Iter

def store (it : Iter) (i : Nat) (v : field.M31) : Iter :=
  { it with slice := it.slice.setAtNat i v }

def bounded : Nat → Iter → (Iter → Iter) → transcript.Transcript →
    Array U8 32#usize → Usize → Result Output
  | 0, it, back, s, _, _ => .ok (s, none, back it)
  | n + 1, it, back, s, b, j =>
      if h : it.i < it.slice.len then do
        let limb := it.slice[it.i]
        let it1 := { it with i := it.i + 1 }
        let (s1, b1, j1, v, accepted) ←
          transcript.Transcript.challenge_qm31_loop0_loop0
            { start := 0#u32, «end» := transcript.CHALLENGE_RETRY_LIMIT }
            s b j limb
        if accepted then
          bounded n it1 (fun out => back (store out it.i v)) s1 b1 j1
        else ok (s1, some (.Err ()), back (store it1 it.i v))
      else .ok (s, none, back it)

theorem exhausted (it : Iter) (back : Iter → Iter)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize)
    (h : ¬ it.i < it.slice.len) :
    transcript.Transcript.challenge_qm31_loop0.body it back s b j =
      .ok (.done (s, none, back it)) := by
  simp only [transcript.Transcript.challenge_qm31_loop0.body,
    core.slice.iter.IteratorIterMut.next, dif_neg h, bind_tc_ok]

theorem loop_execution (n : Nat) (it : Iter) (back : Iter → Iter)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize)
    (hn : it.slice.len - it.i = n) :
    transcript.Transcript.challenge_qm31_loop0 it back s b j =
      bounded n it back s b j := by
  induction n generalizing it back s b j with
  | zero =>
      have h : ¬ it.i < it.slice.len := by omega
      rw [transcript.Transcript.challenge_qm31_loop0, loop.eq_def]
      simp only [exhausted it back s b j h, bounded]
  | succ n ih =>
      have h : it.i < it.slice.len := by omega
      have hn' : it.slice.len - (it.i + 1) = n := by omega
      rw [transcript.Transcript.challenge_qm31_loop0, loop.eq_def]
      simp only [transcript.Transcript.challenge_qm31_loop0.body,
        core.slice.iter.IteratorIterMut.next, dif_pos h, bind_tc_ok,
        bounded]
      cases hs : transcript.Transcript.challenge_qm31_loop0_loop0
          { start := 0#u32, «end» := transcript.CHALLENGE_RETRY_LIMIT }
          s b j (it.slice[it.i]) with
      | fail e => simp
      | div => simp
      | ok output =>
          rcases output with ⟨s1, b1, j1, v, accepted⟩
          cases accepted with
          | false => rfl
          | true =>
              simp only [bind_tc_ok, if_true]
              simpa only [transcript.Transcript.challenge_qm31_loop0,
                transcript.Transcript.challenge_qm31_loop0.body,
                core.slice.iter.IteratorIterMut.next, bind_tc_ok, store]
                using ih { it with i := it.i + 1 }
                  (fun out => back (store out it.i v)) s1 b1 j1 hn'

def initial : Array field.M31 4#usize :=
  Array.repeat 4#usize field.M31.ZERO

def initialIter : Iter := ⟨Array.to_slice initial, 0⟩

def finish (out : Output) : Result
    ((core.result.Result field.QM31 transcript.ChallengeSampleExhausted) ×
      transcript.Transcript) :=
  let (s, pending, it) := out
  match pending with
  | none => do
      let limbs := Array.from_slice initial it.slice
      let v0 ← Array.index_usize limbs 0#usize
      let v1 ← Array.index_usize limbs 1#usize
      let v2 ← Array.index_usize limbs 2#usize
      let v3 ← Array.index_usize limbs 3#usize
      ok (.Ok {c0:={a:=v0,b:=v1},c1:={a:=v2,b:=v3}},s)
  | some r => .ok (r, s)

theorem entry_four (s : transcript.Transcript) :
    transcript.Transcript.challenge_qm31 s =
      (do
        let (b, s1) ← transcript.Transcript.squeeze_block s
        let out ← bounded 4 initialIter (fun it => it) s1 b 0#usize
        finish out) := by
  have hlen : initialIter.slice.len - initialIter.i = 4 := by rfl
  simp only [transcript.Transcript.challenge_qm31, Array.to_slice_mut,
    lift, bind_tc_ok, core.slice.Slice.iter_mut]
  cases hs : transcript.Transcript.squeeze_block s with
  | fail e => rfl
  | div => rfl
  | ok pair =>
      rcases pair with ⟨b, s1⟩
      simp only [bind_tc_ok]
      change (do
        let out ← transcript.Transcript.challenge_qm31_loop0 initialIter
          (fun it => it) s1 b 0#usize
        finish out) = _
      rw [loop_execution 4 initialIter (fun it => it) s1 b 0#usize hlen]

theorem rejected_return (s : transcript.Transcript) (it : Iter) :
    finish (s, some (.Err ()), it) = .ok (.Err (), s) := rfl

#print axioms exhausted
#print axioms loop_execution
#print axioms entry_four
#print axioms rejected_return

end AspisV8R19.R137SamplerLimbLoop
