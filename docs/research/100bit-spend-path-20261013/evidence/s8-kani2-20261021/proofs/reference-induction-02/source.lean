import S8Kani2FinishTraversal

set_option autoImplicit false
noncomputable section
namespace S8Kani2ReferenceInduction
open Aeneas Aeneas.Std Result ControlFlow
open S8OwnedP6 S8OwnedP6ValueModel S8OwnedP6Finish S8Kani2FinishTraversal

/-- The extracted reference step is total at every in-range cursor. -/
theorem step_total (raw : Raw) (state : State)
    (hlen : state.1.length ≤ raw.length) (hi : state.2.val < state.1.length) :
    ∃ next, step raw state = .ok next ∧ next.1.length=state.1.length ∧
      next.2.val=state.2.val+1 := by
  have hr : state.2.val < raw.length := by omega
  obtain ⟨row,hread,_⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec raw state.2 hr)
  have hread' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
      raw state.2=.ok row := by
    rw [alloc.vec.Vec.index_slice_index]; exact hread
  obtain ⟨⟨previous,back⟩,hmut,_,hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec state.1 state.2 hi)
  have hmut' : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Q)
      state.1 state.2=.ok (previous,back) := by
    rw [alloc.vec.Vec.index_mut_slice_index]; exact hmut
  have hcap : state.2.val+1 ≤ Usize.max := by
    have hp : state.1.length ≤ Usize.max := state.1.property
    omega
  have sadd : WP.spec (state.2+1#usize : Result Usize)
      (fun n => n.val=state.2.val+1) := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq,show (1#usize).val=1 by decide] using hcap
  obtain ⟨next,hnext,hval⟩ := WP.spec_imp_exists sadd
  refine ⟨(back (modelValue row),next),?_,?_,hval⟩
  · simp only [step,hread',modelValue_success,hmut',hnext,bind_tc_ok]
    rfl
  · rw [congrFun hback (modelValue row)]
    simp only [alloc.vec.Vec.length,alloc.vec.Vec.set,List.length_set]

/-- Finite induction identifies the actual extracted loop with n reference
steps. The exact remaining length determines n, so no unbounded local-step
preservation hypothesis or callee-success premise remains. -/
theorem reference_loop_induction (raw : Raw) (n : Nat) (state : State)
    (hlen : state.1.length ≤ raw.length)
    (remaining : state.2.val+n=state.1.length) :
    finish_owned_loop raw state.1 state.2 =
      (do let final ← steps raw n state; ok final.1) := by
  induction n generalizing state with
  | zero =>
    have stop : ¬ state.2 < alloc.vec.Vec.len state.1 := by
      change ¬ state.2.val < state.1.length
      omega
    rw [finish_owned_loop,loop]
    simp only [extracted_exit raw state stop,steps,bind_tc_ok]
  | succ n ih =>
    have hi : state.2.val < state.1.length := by omega
    have running : state.2 < alloc.vec.Vec.len state.1 := hi
    obtain ⟨next,hs,hsize,hnext⟩ := step_total raw state hlen hi
    have body := extracted_step raw state running
    rw [hs] at body
    simp only [bind_tc_ok] at body
    rw [finish_owned_loop,loop]
    dsimp only
    rw [body]
    simp only [bind_tc_ok,steps,hs]
    simpa only [finish_owned_loop,bind_assoc_eq] using
      ih next (by omega) (by omega)

/-- Initial state: exactly the destination length iterations, including zero. -/
theorem reference_finish_induction (raw : Raw) (old : Weights)
    (hlen : old.length ≤ raw.length) :
    finish_owned raw old =
      (do let final ← steps raw old.length (old,0#usize); ok final.1) := by
  exact reference_loop_induction raw old.length (old,0#usize) hlen (by simp)

#print axioms step_total
#print axioms reference_loop_induction
#print axioms reference_finish_induction
end S8Kani2ReferenceInduction
