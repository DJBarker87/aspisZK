import Port3_PendingInstall

/-! Length and counter frames of successful actual owned row pushes. These
facts require no canonicality/phase bound or separately successful row value. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_PushFrame
open Aeneas Aeneas.Std Result
open S7Kani2AccumulatorLoop (BatchedWeights K)

theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h

theorem push_fields (state after : BatchedWeights) (index : Usize) (power : K) (basis : U32)
    (bound : index.val < state.raw.val.length)
    (success : S7Kani2OwnedPush.push_owned state index power basis = ok after) :
    after.raw.val.length = state.raw.val.length ∧ after.terms = state.terms := by
  obtain ⟨⟨old,back⟩,hmut,_,hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec state.raw index bound)
  have hm : alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) state.raw index = ok (old,back) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hmut
  unfold S7Kani2OwnedPush.push_owned at success
  obtain ⟨row,_,success⟩ := bind_success _ _ _ success
  obtain ⟨bits,_,success⟩ := bind_success _ _ _ success
  obtain ⟨updated,_,success⟩ := bind_success _ _ _ success
  simp only [hm,bind_tc_ok,hback] at success
  have same := Result.ok.inj success
  subst after
  exact ⟨by simp [alloc.vec.Vec.set],rfl⟩

theorem step_fields (basis : Array U32 256#usize) (power : K)
    (next width index : Usize) (state after : S7Kani2AccumulatorLoop.State)
    (bound : index.val < state.2.raw.val.length)
    (success : S7Kani2AccumulatorLoop.step S7JoinRowsTrace.backend basis power next width index state = ok after) :
    after.1 = state.1 ∧ after.2.raw.val.length = state.2.raw.val.length ∧ after.2.terms = state.2.terms := by
  unfold S7Kani2AccumulatorLoop.step at success
  obtain ⟨m,_,success⟩ := bind_success _ _ _ success
  obtain ⟨weights,hpush,success⟩ := bind_success _ _ _ success
  iterate 8 obtain ⟨x,_,success⟩ := bind_success _ _ _ success
  have same := Result.ok.inj success
  subst after
  exact ⟨rfl,push_fields state.2 weights index power m bound hpush⟩

#print axioms bind_success
#print axioms push_fields
#print axioms step_fields
end AspisR1.Port3_PushFrame
end
