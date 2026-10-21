import S2OwnedSourceInstallationV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS2OwnedStage1.FrameOperationsTotal

theorem deref_val (bytes : alloc.vec.Vec U8) :
    (alloc.vec.Vec.deref bytes).val=bytes.val := by
  unfold alloc.vec.Vec.deref
  rfl

/-- Mathematical slice witness; the theorem below concerns the actual emitted
Vec.index operation on the original Vec, not a replacement source carrier. -/
def segment (bytes : Slice U8) (start finish : Usize) : Slice U8 :=
  ⟨(bytes.val.drop start.val).take (finish.val-start.val), by
    have hb := bytes.property
    simp only [List.length_take,List.length_drop]
    omega⟩

theorem segment_val (bytes : Slice U8) (start finish : Usize) :
    (segment bytes start finish).val=(bytes.val.drop start.val).take (finish.val-start.val) := rfl

theorem range_total (bytes : alloc.vec.Vec U8) (start finish : Usize)
    (hs : start.val ≤ finish.val) (hf : finish.val ≤ bytes.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      bytes {start:=start,«end»:=finish} =
        ok (segment (alloc.vec.Vec.deref bytes) start finish) := by
  change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    (alloc.vec.Vec.deref bytes) {start:=start,«end»:=finish} = _
  simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,segment,Slice.length,List.slice,
    UScalar.le_equiv,deref_val,hs,hf]

theorem prefix_range_total (bytes : alloc.vec.Vec U8) (finish : Usize)
    (hf : finish.val ≤ bytes.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      bytes {«end»:=finish} =
        ok (segment (alloc.vec.Vec.deref bytes) 0#usize finish) := by
  change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
    (alloc.vec.Vec.deref bytes) {«end»:=finish} = _
  simp [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,segment,Slice.length,List.slice,
    UScalar.le_equiv,deref_val,hf]

theorem compact_suffix_total (bytes : alloc.vec.Vec U8)
    (h : bytes.val.length=58295) :
    ∃ selected : Slice U8,
      alloc.vec.Vec.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        bytes {start:=688#usize,«end»:=58295#usize}=ok selected ∧
      selected.val=(bytes.val.drop 688).take 57607 ∧ selected.val.length=57607 := by
  have ha : (688#usize).val=688 := by scalar_tac
  have hz : (58295#usize).val=58295 := by scalar_tac
  have hd : (58295#usize).val-(688#usize).val=57607 := by rw [ha,hz]
  refine ⟨segment (alloc.vec.Vec.deref bytes) 688#usize 58295#usize,
    range_total bytes _ _ (by rw [ha,hz]; omega) (by rw [hz,h]),?_,?_⟩
  · rw [segment_val,deref_val,hd,ha]
  · rw [segment_val,deref_val,hd,ha]
    simp only [List.length_take,List.length_drop,h]

theorem tag_read_total (bytes : alloc.vec.Vec U8) (h : bytes.val.length=58295) :
    ∃ byte : U8,
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U8)
        bytes 696#usize=ok byte ∧ bytes.val[696]?=some byte := by
  obtain ⟨byte,hr,hbyte⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec bytes 696#usize (by scalar_tac))
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
#print axioms prefix_range_total
#print axioms compact_suffix_total
#print axioms tag_read_total
#print axioms copy_total
end AspisS2OwnedStage1.FrameOperationsTotal
