import Aeneas.Std.RangeIter

/-! Reuse the standard-library step_by specs, including the saturating last
chunk of length three at the seven-input internal-constant boundary. -/
set_option autoImplicit false
namespace AspisR1.FJh_M31DotChunkIterator
open Aeneas Aeneas.Std Result WP
abbrev Range := core.ops.range.Range Usize
abbrev Iter := core.iter.adapters.step_by.StepBy Range

def initial (len : Usize) : Iter :=
  { iter := { start := 0#usize, «end» := len }, step_by := 4#usize }

theorem initial_source (len : Usize) :
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      ({ start := 0#usize, «end» := len } : Range) 4#usize = .ok (initial len) := by
  have hnonzero : (4#usize).val ≠ 0 := by decide
  simp only [core.iter.traits.iterator.Iterator.step_by.trait_default,
    core.iter.traits.iterator.Iterator.step_by.default,if_neg hnonzero]
  rfl

theorem next_step (iter : Iter) (hstep : iter.step_by.val = 4)
    (hactive : iter.iter.start.val < iter.iter.end.val) :
    ∃ next : Iter,
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter =
          .ok (some iter.iter.start,next) ∧
      next.iter.start.val = min (iter.iter.start.val+4) iter.iter.end.val ∧
      next.iter.end = iter.iter.end ∧ next.step_by.val = 4 := by
  have hpositive : iter.step_by.val > 0 := by rw [hstep]; decide
  obtain ⟨pair,hrun,hpost⟩ := WP.spec_imp_exists
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec iter hpositive)
  rcases pair with ⟨o,next⟩
  have hcase := hpost.1
  rw [if_pos hactive] at hcase
  have ho := hcase.1
  have hinc := hcase.2
  rw [ho] at hrun
  rw [hstep] at hinc
  refine ⟨next,hrun,hinc,hpost.2.1,?_⟩
  exact (congrArg UScalar.val hpost.2.2).trans hstep

theorem next_done (iter : Iter) (hstop : iter.iter.start.val ≥ iter.iter.end.val) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter = .ok (none,iter) := by
  obtain ⟨pair,hrun,hpost⟩ := WP.spec_imp_exists
    (core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec iter hstop)
  rcases pair with ⟨o,next⟩
  rw [hpost.1,hpost.2] at hrun
  exact hrun

#print axioms initial_source
#print axioms next_step
#print axioms next_done
end AspisR1.FJh_M31DotChunkIterator
