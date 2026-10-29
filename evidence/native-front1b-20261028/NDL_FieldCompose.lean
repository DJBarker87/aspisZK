import NDL_FieldDecode
set_option autoImplicit false
noncomputable section
namespace NDL_FieldCompose
open Aeneas Aeneas.Std Result

theorem reference_cut (bytes : Slice U8) (i : Usize)
    (fits : 32*(i.val+1)<UScalar.size .Usize) (part : Array U8 32#usize)
    (selection : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      {start:=Usize.wrapping_mul i 32#usize,
       «end»:=Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize}=ok part.to_slice) :
    NDL_FieldRef.field_ref bytes i=ok (NBG_WideBytes.limbs part) := by
  have shape : NDL_FieldRef.field_ref bytes i = (do
      let range ← NDL_Reference.range_ref i
      let selected ← core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
        {start:=range.1, «end»:=range.2}
      NDL_FieldRef.decode_ref selected) := by
    simp only [NDL_FieldRef.field_ref,NDL_Reference.range_ref,bind_assoc_eq]
    rfl
  rw [shape,NDL_FieldAssociation.offsets i fits]
  simp only [bind_tc_ok,selection,NDL_FieldDecode.decode]

theorem selection (bytes : Slice U8) (i : Usize) (part : Array U8 32#usize)
    (bound : 32*(i.val+1)≤bytes.val.length)
    (same : part.val=(bytes.val.drop (32*i.val)).take 32) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      {start:=Usize.wrapping_mul i 32#usize,
       «end»:=Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize}=ok part.to_slice := by
  have size : bytes.val.length<UScalar.size .Usize := by
    have h := bytes.property
    simp only [UScalar.size,UScalarTy.numBits,Usize.max,Usize.numBits] at h ⊢
    omega
  have offsets := NBQ_FieldOffsets.value i (by omega)
  simp only [Slice.index_SliceIndexRangeUsizeSliceInst]
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index
  split
  · congr 1
    apply Subtype.ext
    simp only [Array.to_slice,List.slice,offsets.1,offsets.2]
    have diff : 32*(i.val+1)-32*i.val=32 := by omega
    simpa only [diff] using same.symm
  · rename_i h
    apply False.elim
    apply h
    constructor
    · change Usize.wrapping_mul i 32#usize ≤ Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize
      scalar_tac
    · change (Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize).val ≤ bytes.val.length
      rw [offsets.2];exact bound

/-- Same input, same selection, full returned eight-word value. No decoder
success, selected slice, or output is supplied independently by the caller. -/
theorem cohort (bytes : Slice U8) (i : Usize)
    (bound : 32*(i.val+1)≤bytes.val.length)
    (canonical : ∀ part : Array U8 32#usize,
      part.val=(bytes.val.drop (32*i.val)).take 32 → NCJ_FieldTotal.Canonical part) :
    NDL_FieldRef.field_ref bytes i = (do
      let value ← FIo_Native.weights.field bytes i
      FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value) := by
  obtain ⟨part,same,run,_⟩ := NCJ_FieldTotal.source bytes i bound canonical
  have size : bytes.val.length<UScalar.size .Usize := by
    have h := bytes.property
    simp only [UScalar.size,UScalarTy.numBits,Usize.max,Usize.numBits] at h ⊢
    omega
  rw [reference_cut bytes i (by omega) part (selection bytes i part bound same),run]
  simp only [bind_tc_ok]
  rfl

#print axioms reference_cut
#print axioms selection
#print axioms cohort
end NDL_FieldCompose
end
