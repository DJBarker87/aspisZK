import NEV_AccumulateCarriers
import NEV_AccumulateRaw.Funs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NEV_BorrowMaps
open Aeneas Aeneas.Std Result NEV_AccumulateCarriers
/-- Same indexed value through the full-vector nominal carrier map. -/
theorem vector_read {A B : Type} (f : A → B) (v : alloc.vec.Vec A) (index : Usize)
    (inside : index.val<v.val.length) :
    ∃ value, Slice.index_usize v.deref index=ok value ∧
      Slice.index_usize (mapVec f v).deref index=ok (f value) := by
  obtain ⟨value,read,point⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec v index inside)
  have mappedInside : index.val<(mapVec f v).val.length := by
    simpa only [mapVec,List.length_map] using inside
  obtain ⟨mapped,mappedRead,mappedAt⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec (mapVec f v) index mappedInside)
  have mappedAt' : mapped=f (v.val[index.val]'inside) := by
    simpa only [mapVec,List.getElem_map] using mappedAt
  have same : mapped=f value := mappedAt'.trans (congrArg f point.symm)
  refine ⟨value,read,?_⟩
  exact mappedRead.trans (congrArg Result.ok same)

/-- The actual reached getter and the installed cohort read have the SAME
input index and returned four raw words, on the caller's length domain. -/
theorem weight_read (ops : AspisR1.Port3_NativeQueryBody.Ops)
    (v : alloc.vec.Vec RawQ) (index : Usize) (inside : index.val<v.val.length) :
    ∃ q, NEV_AccumulateRaw.accumulated_weight_at v.deref index=ok q ∧
      (NBF_RowInstall.install ops).op12 (mapVec toQ v).deref index=ok (toQ q) := by
  obtain ⟨q,read,mapped⟩ := vector_read toQ v index inside
  exact ⟨q,read,mapped⟩
#print axioms vector_read
#print axioms weight_read
end NEV_BorrowMaps
end
