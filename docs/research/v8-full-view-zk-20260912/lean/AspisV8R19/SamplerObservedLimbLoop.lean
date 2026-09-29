import AspisV8R19.SamplerObservedLimbBridge
import AspisV8R19.SamplerLimbLoop

/-! Instrumented mutable-limb iteration retains the complete per-limb
observation and the original deferred write-back closures. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservedLimbLoop
open Aeneas Aeneas.Std Result ControlFlow AspisR72Sampler
open SamplerObservation SamplerObservedLaws
open SamplerLimbLoop (Iter Output store initial initialIter finish)

def bounded : Nat → Iter → (Iter → Iter) → transcript.Transcript →
    Array U8 32#usize → Usize → Observed Output
  | 0,it,back,s,_,_ => pure (s,none,back it)
  | n+1,it,back,s,b,j =>
      if h : it.i < it.slice.len then do
        let limb := it.slice[it.i]
        let it1 := {it with i:=it.i+1}
        let (s1,b1,j1,v,accepted) ← SamplerObservedSource.challenge_qm31_loop0_loop0
          {start:=0#u32, «end»:=transcript.CHALLENGE_RETRY_LIMIT} s b j limb
        if accepted then bounded n it1 (fun out => back (store out it.i v)) s1 b1 j1
        else pure (s1,some (.Err ()),back (store it1 it.i v))
      else pure (s,none,back it)

theorem exhausted (it : Iter) (back : Iter → Iter) (s : transcript.Transcript)
    (b : Array U8 32#usize) (j : Usize) (h : ¬it.i < it.slice.len) (history : Trace) :
    SamplerObservedSource.challenge_qm31_loop0.body it back s b j history =
      .ok (.done (s,none,back it),history) := by
  simp only [SamplerObservedSource.challenge_qm31_loop0.body,
    core.slice.iter.IteratorIterMut.next,dif_neg h,bind_apply,lift_apply,bind_tc_ok,pure_apply]

theorem loop_execution (n : Nat) (it : Iter) (back : Iter → Iter)
    (s : transcript.Transcript) (b : Array U8 32#usize) (j : Usize)
    (hn : it.slice.len-it.i=n) (history : Trace) :
    SamplerObservedSource.challenge_qm31_loop0 it back s b j history =
      bounded n it back s b j history := by
  induction n generalizing it back s b j history with
  | zero =>
      have h : ¬it.i < it.slice.len := by omega
      rw [SamplerObservedSource.challenge_qm31_loop0,loop_unfold]
      simp only [exhausted it back s b j h,bounded,pure_apply,bind_tc_ok]
  | succ n ih =>
      have h : it.i < it.slice.len := by omega
      have hn' : it.slice.len-(it.i+1)=n := by omega
      rw [SamplerObservedSource.challenge_qm31_loop0,loop_unfold]
      simp only [SamplerObservedSource.challenge_qm31_loop0.body,
        core.slice.iter.IteratorIterMut.next,dif_pos h,bind_apply,lift_apply,bind_tc_ok,bounded]
      cases hs : SamplerObservedSource.challenge_qm31_loop0_loop0
          {start:=0#u32, «end»:=transcript.CHALLENGE_RETRY_LIMIT}
          s b j (it.slice[it.i]) history with
      | fail e => simp
      | div => simp
      | ok output =>
          rcases output with ⟨⟨s1,b1,j1,v,accepted⟩,observed⟩
          cases accepted with
          | false => simp only [bind_tc_ok,Bool.false_eq_true,if_false,pure_apply,store]
          | true =>
              simp only [bind_tc_ok,if_true,pure_apply]
              simpa only [SamplerObservedSource.challenge_qm31_loop0,
                SamplerObservedSource.challenge_qm31_loop0.body,
                core.slice.iter.IteratorIterMut.next,bind_tc_ok,store]
                using ih {it with i:=it.i+1} (fun out => back (store out it.i v)) s1 b1 j1 hn' observed

theorem entry_four (s : transcript.Transcript) (history : Trace) :
    SamplerObservedSource.challenge_qm31 s history =
      (do
        let ((b,s1),t) ← SamplerObservedSource.squeeze_block s history
        let (out,t1) ← bounded 4 initialIter (fun it => it) s1 b 0#usize t
        let result ← finish out
        ok (result,t1)) := by
  have hlen : initialIter.slice.len-initialIter.i=4 := by rfl
  simp only [SamplerObservedSource.challenge_qm31,Array.to_slice_mut,lift,bind_apply,
    lift_apply,bind_tc_ok,core.slice.Slice.iter_mut]
  cases hs : SamplerObservedSource.squeeze_block s history with
  | fail e => simp
  | div => simp
  | ok pair =>
      rcases pair with ⟨⟨b,s1⟩,t⟩
      simp only [bind_tc_ok]
      erw [loop_execution 4 initialIter (fun it => it) s1 b 0#usize hlen t]
      cases hb : bounded 4 initialIter (fun it => it) s1 b 0#usize t with
      | fail e => simp
      | div => simp
      | ok output =>
          rcases output with ⟨⟨s2,pending,it⟩,t1⟩
          cases pending <;>
            simp [finish,bind_apply,lift_apply,pure_apply,map_apply,bind_assoc,bind_tc_ok,initial]

#print axioms exhausted
#print axioms loop_execution
#print axioms entry_four
end AspisV8R19.SamplerObservedLimbLoop
