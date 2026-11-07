import NMT_R2_InputSlice
set_option autoImplicit false
noncomputable section
namespace NMT_R2_InputRoundtrip
open Aeneas Aeneas.Std NMT_345 RSL NMT_R2_Bytes

theorem from_native (bytes : Slice U8) (length : bytes.val.length = 1880) :
 NMT_R2_InputSlice.statement (bytes.val.map byte) (by simpa using length) = bytes := by
 apply Subtype.ext
 exact native_bytes bytes.val
#print axioms from_native
end NMT_R2_InputRoundtrip
end
