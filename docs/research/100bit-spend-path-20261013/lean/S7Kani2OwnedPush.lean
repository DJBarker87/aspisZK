import S7Kani2OwnedRow

/-! Exact emitted owned Vec push with its concrete Aeneas indexing/setter
semantics. No whole-Vec source equivalence or allocation premise is hidden. -/
set_option autoImplicit false
namespace S7Kani2OwnedPush
open Aeneas Aeneas.Std Result
open S7Kani2AccumulatorLoop (BatchedWeights K)
open S7Kani2OwnedRow (Row residue_owned limb)

def push_owned (weights : BatchedWeights) (index : Usize) (power : K) (basis : U32) :
    Result BatchedWeights := do
  let row ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) weights.raw index
  let i ← lift (weights.terms &&& 3#usize)
  let updated ← residue_owned row power basis (i = 3#usize)
  let (_, index_mut_back) ← alloc.vec.Vec.index_mut
    (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) weights.raw index
  let v := index_mut_back updated
  ok {weights with raw := v}

/-- The emitted push is total on its bounded local row domain, and is exactly
one Vec.set. This exposes the complete frame, rather than only row values. -/
theorem push_total_frame (weights : BatchedWeights) (index : Usize) (power : K) (basis : U32)
    (hindex : index.val<weights.raw.length)
    (safe : ∀ row, alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
        weights.raw index=ok row →
      ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
        raw.val+(limb power j).val*basis.val<2^64) :
    ∃ row updated,
      push_owned weights index power basis = ok {weights with raw := weights.raw.set index updated} ∧
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row) weights.raw index=ok row ∧
      residue_owned row power basis ((weights.terms &&& 3#usize)=3#usize)=ok updated := by
  obtain ⟨row,hread,_⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec weights.raw index hindex)
  have hr : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
      weights.raw index=ok row := hread
  obtain ⟨updated,hupdated⟩ := S7Kani2OwnedRow.row_total row power basis _ (safe row hr)
  obtain ⟨⟨old,back⟩,hmut,_,hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec weights.raw index hindex)
  have hm : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Row)
      weights.raw index = ok (old,back) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hmut
  refine ⟨row,updated,?_,hr,hupdated⟩
  simp only [push_owned,hr,lift,bind_tc_ok,hupdated,hm,hback]
  rfl

#print axioms push_total_frame
end S7Kani2OwnedPush
