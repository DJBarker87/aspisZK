import R1Z.PV_CBL_ShaBytes
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteCodecValue
set_option autoImplicit false
def load (a b c d : U8) : U32 :=
  ((U32.wrapping_shl (UScalar.cast .U32 a) 24#u32 |||
    U32.wrapping_shl (UScalar.cast .U32 b) 16#u32) |||
    U32.wrapping_shl (UScalar.cast .U32 c) 8#u32) ||| UScalar.cast .U32 d
def store (w : U32) : Array U8 4#usize :=
  Array.make 4#usize [UScalar.cast .U8 (U32.wrapping_shr w 24#u32),
    UScalar.cast .U8 (U32.wrapping_shr w 16#u32),
    UScalar.cast .U8 (U32.wrapping_shr w 8#u32),UScalar.cast .U8 w]
theorem store_source (w : U32) : PV_CBL_ShaBytes.sha_store_be4 w = ok (store w) := rfl
#print axioms load
#print axioms store
#print axioms store_source
end R1Z.PV_CBL_ByteCodecValue
