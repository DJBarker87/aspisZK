import NDL_FieldRef.Funs
import NDL_FieldAssociation
set_option autoImplicit false
noncomputable section
namespace NDL_FieldDecode
open Aeneas Aeneas.Std Result

theorem decode (part : Array U8 32#usize) :
    NDL_FieldRef.decode_ref part.to_slice = ok (NBG_WideBytes.limbs part) := by
  simp [NDL_FieldRef.decode_ref,Slice.index_usize,Array.to_slice,
    part.property,NBG_WideBytes.limbs,NBG_WideBytes.word,lift,bind_tc_ok]

/-- Full successful native-window result, including all eight returned words.
The byte carrier is the SAME exact32 part used by the decoder. -/
theorem window (part : Array U8 32#usize) (canonical : NCJ_FieldTotal.Canonical part) :
    (do
      let value ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes part.to_slice
      let value ← core.option.Option.unwrap value
      FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value) =
      NDL_FieldRef.decode_ref part.to_slice := by
  rw [NBG_WideBytes.bytes_result,NCJ_FieldTotal.limbs part canonical,decode]
  simp only [bind_tc_ok,core.option.Option.unwrap]
  rfl

#print axioms decode
#print axioms window
end NDL_FieldDecode
end
