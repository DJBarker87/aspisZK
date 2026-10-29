import NBG_WideBytes
set_option autoImplicit false
noncomputable section
namespace NBQ_FieldPort
open Aeneas Aeneas.Std Result AspisR1
/-- Full Result on the SAME selected32-byte carrier. No reselected bytes or
parser success is supplied; canonicality is checked by from_limbs. -/
theorem selected (bytes : Slice U8) (i : Usize) (part : Array U8 32#usize)
    (selection : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
      {start:=Usize.wrapping_mul i 32#usize,
       «end»:=Usize.wrapping_mul (Usize.wrapping_add i 1#usize) 32#usize}=ok part.to_slice) :
    FIo_Native.weights.field bytes i = (do
      let decoded ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
        (NBG_WideBytes.limbs part)
      core.option.Option.unwrap decoded) := by
  simp only [FIo_Native.weights.field,lift,bind_tc_ok,selection,NBG_WideBytes.bytes_result]
#print axioms selected
end NBQ_FieldPort
