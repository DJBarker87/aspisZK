import S2OwnedSourceInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.FrameOperationsTotal

/-- Mathematical slice witness; the theorem below concerns the actual emitted
Vec.index operation on the original Vec, not a replacement source carrier. -/
def segment (bytes : Slice U8) (start finish : Usize) : Slice U8 :=
  ⟨(bytes.val.drop start.val).take (finish.val-start.val), by
    have hb := bytes.property
    simp only [List.length_take,List.length_drop]
    omega⟩

theorem range_total (bytes : alloc.vec.Vec U8) (start finish : Usize)
    (hs : start.val ≤ finish.val) (hf : finish.val ≤ bytes.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=start,«end»:=finish} =
        ok (segment (alloc.vec.Vec.deref bytes) start finish) := by
  rw [alloc.vec.Vec.index_slice_index]
  simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,segment,Slice.length,List.slice,
    UScalar.le_equiv,hs,hf]

theorem compact_suffix_total (bytes : alloc.vec.Vec U8)
    (h : bytes.val.length=58295) :
    ∃ selected : Slice U8,
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes {start:=688#usize,«end»:=58295#usize}=ok selected ∧
      selected.val=(bytes.val.drop 688).take 57607 ∧ selected.val.length=57607 := by
  refine ⟨segment (alloc.vec.Vec.deref bytes) 688#usize 58295#usize,
    range_total bytes _ _ (by scalar_tac) (by simpa using h.ge),rfl,?_⟩
  simp only [segment,List.length_take,List.length_drop]
  change min 57607 (bytes.val.length-688)=57607
  omega

theorem tag_read_total (bytes : alloc.vec.Vec U8) (h : bytes.val.length=58295) :
    ∃ byte : U8,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8)
        bytes 696#usize=ok byte ∧ bytes.val[696]?=some byte := by
  obtain ⟨byte,hr,hbyte⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec bytes 696#usize (by simpa only [h] using (by decide : 696<58295)))
  refine ⟨byte,?_,?_⟩
  · rw [alloc.vec.Vec.index_slice_index]
    exact hr
  · rw [List.getElem?_eq_getElem (by omega)]
    exact congrArg some hbyte.symm

theorem copy_total (checkpoint source : Slice U8)
    (h : checkpoint.val.length=source.val.length) :
    core.slice.Slice.copy_from_slice core.marker.CopyU8 checkpoint source=ok source := by
  obtain ⟨out,hr,he⟩ := WP.spec_imp_exists
    (core.slice.Slice.copy_from_slice.step_spec core.marker.CopyU8 checkpoint source h)
  simpa only [he] using hr

#print axioms range_total
#print axioms compact_suffix_total
#print axioms tag_read_total
#print axioms copy_total
end AspisS2OwnedStage1.FrameOperationsTotal
