import R1Z.PV_CBL_DigestBytesValue
import R1Z.PV_CBL_FallbackStateCodec
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_DigestBytesList
set_option autoImplicit false
theorem list (state : Array U32 8#usize) :
    (PV_CBL_DigestBytesValue.value state).val =
      state.val.flatMap (fun word => (PV_CBL_ByteCodecValue.store word).val) := by
  rw [← PV_CBL_FallbackStateCodec.encode_decode state]
  rfl
#print axioms list
end R1Z.PV_CBL_DigestBytesList
