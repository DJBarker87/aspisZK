import Aeneas
import Aeneas.Std.RangeIter
set_option autoImplicit false
namespace AspisR1.CuSavingsDelayedIterator
open Aeneas Aeneas.Std Result WP
abbrev Iter := core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)

def At (count : Nat) (iter : Iter) : Prop :=
  iter.iter.start.val = min (4*count) 26 ∧ iter.iter.end.val = 26 ∧ iter.step_by.val = 4

theorem next_spec (iter : Iter) (hstep : iter.step_by.val = 4) :
    ∃ (opt : Option Usize) (next : Iter),
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter = .ok (opt,next) ∧
      (if iter.iter.start.val < iter.iter.end.val then
        opt = some iter.iter.start ∧ next.iter.start.val = min (iter.iter.start.val+4) iter.iter.end.val
       else opt = none ∧ next.iter.start = iter.iter.start) ∧
      next.iter.end = iter.iter.end ∧ next.step_by = iter.step_by := by
  obtain ⟨pair,hn,hpost⟩ := WP.spec_imp_exists
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_UScalar_spec
      (fun _ => rfl) (fun _ _ => rfl) iter (by omega))
  rcases pair with ⟨opt,next⟩
  refine ⟨opt,next,hn,?_,hpost.2.1,hpost.2.2⟩
  simpa only [hstep] using hpost.1

theorem next_step (count : Nat) (iter : Iter) (h : At count iter) (hc : count < 7) :
    ∃ next : Iter,
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some iter.iter.start,next) ∧ At (count+1) next := by
  obtain ⟨opt,next,hn,hpost,he,hs⟩ := next_spec iter h.2.2
  have hstart : iter.iter.start.val = 4*count := by
    rw [h.1];apply Nat.min_eq_left;omega
  have hl : iter.iter.start.val < iter.iter.end.val := by omega
  rw [if_pos hl] at hpost
  refine ⟨next,by simpa only [hpost.1] using hn,?_,?_,?_⟩
  · rw [hpost.2,hstart,h.2.1]
    congr 1 <;> omega
  · rw [he];exact h.2.1
  · rw [hs];exact h.2.2

theorem next_done (iter : Iter) (h : At 7 iter) :
    ∃ next : Iter,
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter = .ok (none,next) := by
  obtain ⟨opt,next,hn,hpost,he,hs⟩ := next_spec iter h.2.2
  have hl : ¬ iter.iter.start.val < iter.iter.end.val := by
    have hv := h.1;norm_num at hv;omega
  rw [if_neg hl] at hpost
  exact ⟨next,by simpa only [hpost.1] using hn⟩

#print axioms next_spec
#print axioms next_step
#print axioms next_done
end AspisR1.CuSavingsDelayedIterator
