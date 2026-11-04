import NGC_FinishFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_ValueBridge
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- Total SAME pending-row value; every output coordinate is the exact
natural residue, for full U64 inputs and any valid raw-row index. -/
theorem value (b : verifier.BatchedWeights) (index : Usize) (inside : index.val<b.raw.val.length) :
 ∃ row : S8OwnedP6ValueModel.Row,
 alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice S8OwnedP6ValueModel.Row) b.raw index=ok row ∧
 S8Kani2MutableValue.F.value (⟨b.raw,b.terms⟩ : S8Kani2MutableValue.F.BW) index=
  ok (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row)) ∧
 Port3_FlushInstall.Canonical (Port3_FlushInstall.fromMutable
  (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row))) ∧
 ∀ j : Fin 4,
 (S8OwnedP6ValueModel.coordinate (S8OwnedP6Finish.modelValue row) j).val=
  (S8OwnedP6ValueModel.rowAt row j).val%2147483647 := by
 obtain ⟨row,read,_⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b.raw index inside)
 have read' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice S8OwnedP6ValueModel.Row) b.raw index=ok row := by
  rw [alloc.vec.Vec.index_slice_index]
  exact read
 exact ⟨row,read',S8Kani2FinishReferenceJoin.value_reference ⟨b.raw,b.terms⟩ index row read',
  Port3_FlushInstall.model_canonical row,fun j=>(S8OwnedP6Finish.modelValue_coordinates row j).1⟩
#print axioms value
end AspisR1.NGC_ValueBridge
end
