import Aeneas
set_option autoImplicit false
namespace AspisS1AcceptedSliceRange
open Aeneas Aeneas.Std Result WP

/-- Accepted typed Std range access has its exact frame length and guards.
No length/success fact is taken from an unrelated slice. Native memory/abort
correspondence is outside this logical Std-model theorem. -/
theorem accepted_range {A : Type} (input output : Slice A) (start stop : Usize)
    (success : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice A)
      input {start:=start,«end»:=stop}=ok output) :
    start.val ≤ stop.val ∧ stop.val ≤ input.length ∧ output.length=stop.val-start.val := by
  simp only [Slice.index_SliceIndexRangeUsizeSliceInst] at success
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at success
  split at success
  · rename_i bound
    have ⟨value,call,facts⟩ := spec_imp_exists
      (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
        {start:=start,«end»:=stop} input bound.1 bound.2)
    have index : core.slice.index.SliceIndexRangeUsizeSlice.index {start:=start,«end»:=stop} input=ok output := by
      simp only [core.slice.index.SliceIndexRangeUsizeSlice.index,if_pos bound]
      exact success
    have equal := Result.ok.inj (call.symm.trans index)
    subst value
    exact ⟨by scalar_tac,by scalar_tac,facts.2⟩
  · cases success

#print axioms accepted_range
end AspisS1AcceptedSliceRange
