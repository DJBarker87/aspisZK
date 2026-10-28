import NBQ_FieldPort
import NBQ_FieldOffsets
set_option autoImplicit false
noncomputable section
namespace NBQ_FieldTotal
open Aeneas Aeneas.Std Result AspisR1
/-- The range and exact32-byte carrier are DERIVED from source-valid bounds,
not supplied as a successful decoder or selected slice observation. -/
theorem range (bytes : Slice U8) (i : Usize)
    (bound : 32*(i.val+1)≤bytes.val.length) :
    ∃ part : Array U8 32#usize,
      part.val=(bytes.val.drop (32*i.val)).take 32 ∧
      FIo_Native.weights.field bytes i = (do
        let decoded ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
          (NBG_WideBytes.limbs part)
        core.option.Option.unwrap decoded) := by
  have size : bytes.val.length<UScalar.size .Usize := by scalar_tac
  have offsets := NBQ_FieldOffsets.value i (by omega)
  let data := (bytes.val.drop (32*i.val)).take 32
  have len : data.length=32 := by
    simp only [data,List.length_take,List.length_drop];omega
  let part : Array U8 32#usize := ⟨data,len⟩
  refine ⟨part,rfl,NBQ_FieldPort.selected bytes i part ?_⟩
  simp only [Slice.index_SliceIndexRangeUsizeSliceInst]
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index
  split
  · congr 1
    apply Subtype.ext
    simp only [Array.to_slice,part,List.slice,offsets.1,offsets.2]
    have diff : 32*(i.val+1)-32*i.val=32 := by omega
    simp only [diff]
  · rename_i h
    exact (h ⟨by rw [offsets.1,offsets.2];omega,by rw [offsets.2];exact bound⟩).elim
#print axioms range
end NBQ_FieldTotal
