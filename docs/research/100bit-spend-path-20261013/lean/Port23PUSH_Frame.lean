import Port23PUSH_Source
set_option autoImplicit false
noncomputable section
namespace Port23PUSH
open Aeneas Aeneas.Std Result

/-- Full-result outer normalization of the *mutable source-emitted* push.
The row update is unchanged, with its external mutable-array primitive explicit.
No row-success, overflow, canonicality or in-range premise is imposed. -/
theorem push_complete (arrayIntoIter : ArrayIntoIter)
    (b : verifier.BatchedWeights) (index : Usize) (power : field.QM31) (basis : field.M31) :
    verifier.BatchedWeights.push arrayIntoIter b index power basis =
      (do
        let row ← alloc.vec.Vec.index
          (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) b.raw index
        let updated ← verifier.update_residue_row arrayIntoIter row power basis
          ((b.terms &&& 3#usize) = 3#usize)
        ok {b with raw := b.raw.set index updated}) := by
  by_cases bound : index.val < b.raw.val.length
  · obtain ⟨row,hr,hrow⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_usize_spec b.raw index bound)
    obtain ⟨⟨old,back⟩,hm,hold,hback⟩ := WP.spec_imp_exists
      (alloc.vec.Vec.index_mut_usize_spec b.raw index bound)
    have hm' : alloc.vec.Vec.index_mut
        (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) b.raw index =
        ok (old,back) := by
      rw [alloc.vec.Vec.index_mut_slice_index]
      exact hm
    have hr' : alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) b.raw index =
        ok row := hr
    have oldrow : old = row := by
      simpa only [hold] using hrow.symm
    simp only [verifier.BatchedWeights.push, lift, bind_tc_ok, hm', hr', hback, oldrow]
    rfl
  · simp [verifier.BatchedWeights.push, alloc.vec.Vec.index_mut_slice_index,
      alloc.vec.Vec.index_mut_usize, alloc.vec.Vec.index_usize, bound,
      alloc.vec.Vec.index, core.slice.index.SliceIndexUsizeSlice, Slice.index_usize, lift]

/-- An invalid index rejects before entering either row loop. -/
theorem push_bad_index (arrayIntoIter : ArrayIntoIter)
    (b : verifier.BatchedWeights) (index : Usize) (power : field.QM31) (basis : field.M31)
    (bad : ¬ index.val < b.raw.val.length) :
    verifier.BatchedWeights.push arrayIntoIter b index power basis = fail Error.arrayOutOfBounds := by
  rw [push_complete]
  simp [alloc.vec.Vec.index, core.slice.index.SliceIndexUsizeSlice,
    alloc.vec.Vec.index_usize, Slice.index_usize, bad]

private theorem bind_ok {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (do let x ← m; k x) = ok out) : ∃ x, m = ok x ∧ k x = ok out := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => cases h
  | div => cases h

/-- Entire successful Vec frame, not only equality of the selected row.
No bound or arithmetic domain is assumed. Failure/div behavior is in push_complete. -/
theorem push_success_frame (arrayIntoIter : ArrayIntoIter)
    (b after : verifier.BatchedWeights) (index : Usize) (power : field.QM31) (basis : field.M31)
    (run : verifier.BatchedWeights.push arrayIntoIter b index power basis = ok after) :
    ∃ row updated,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize))
        b.raw index = ok row ∧
      verifier.update_residue_row arrayIntoIter row power basis
        ((b.terms &&& 3#usize) = 3#usize) = ok updated ∧
      after = {b with raw := b.raw.set index updated} := by
  rw [push_complete] at run
  obtain ⟨row,hr,run⟩ := bind_ok _ _ _ run
  obtain ⟨updated,hu,run⟩ := bind_ok _ _ _ run
  exact ⟨row,updated,hr,hu,(Result.ok.inj run).symm⟩

#print axioms push_complete
#print axioms push_bad_index
#print axioms bind_ok
#print axioms push_success_frame
end Port23PUSH
end
