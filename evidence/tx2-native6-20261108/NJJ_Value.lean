import NJC_OrderedCalls
set_option autoImplicit false
noncomputable section
namespace NJJ_Value
open Aeneas Aeneas.Std Result
open S8Kani2MutableValue S8Kani2FinishReferenceJoin S8OwnedP6ValueModel S8OwnedP6Finish

/-- Complete source Result on the exact selected row, for every U64 limb.
No canonicality, endpoint result or successful-read hypothesis. -/
theorem source (self : F.BW) (i : Usize) (inside : i.val<self.raw.length) :
 ∃ row : Row, self.raw.val[i.val]?=some row ∧
 F.value self i=ok (toFinish (modelValue row)) := by
 obtain ⟨row,read,lookup⟩ := WP.spec_imp_exists
  (alloc.vec.Vec.index_usize_spec self.raw i inside)
 have read' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row) self.raw i=ok row := by
  rw [alloc.vec.Vec.index_slice_index];exact read
 refine ⟨row,?_,value_reference self i row read'⟩
 rw [List.getElem?_eq_getElem inside,lookup]

/-- Proven source projection for K025's single-row replacement. Width1 is
not asserted of the caller: its arbitrary indexed source row is selected
internally from its bound, and every other row is irrelevant to value(). -/
theorem projection (self : F.BW) (i : Usize) (inside : i.val<self.raw.length) :
 ∃ row : Row, self.raw.val[i.val]?=some row ∧
 F.value self i=F.value (⟨⟨[row],by simp;scalar_tac⟩,self.terms⟩ : F.BW) 0#usize := by
 obtain ⟨row,lookup,result⟩ := source self i inside
 have singleton : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Row)
  (⟨[row],by simp;scalar_tac⟩ : alloc.vec.Vec Row) 0#usize=ok row := by rfl
 refine ⟨row,lookup,?_⟩
 rw [result,value_reference _ _ row singleton]

#print axioms source
#print axioms projection
end NJJ_Value
