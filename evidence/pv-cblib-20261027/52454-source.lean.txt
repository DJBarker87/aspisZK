import R1Z.PV_CBL_ByteStoreRead
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ByteStoreValue
set_option autoImplicit false
def byte (w : U32) (j : Nat) : U8 :=
  match j with
  | 0 => UScalar.cast .U8 (U32.wrapping_shr w 24#u32)
  | 1 => UScalar.cast .U8 (U32.wrapping_shr w 16#u32)
  | 2 => UScalar.cast .U8 (U32.wrapping_shr w 8#u32)
  | _ => UScalar.cast .U8 w
theorem val (w : U32) : (PV_CBL_ByteCodecValue.store w).val =
    [UScalar.cast .U8 (U32.wrapping_shr w 24#u32),
     UScalar.cast .U8 (U32.wrapping_shr w 16#u32),
     UScalar.cast .U8 (U32.wrapping_shr w 8#u32),UScalar.cast .U8 w] := rfl
#print axioms byte
#print axioms val
end R1Z.PV_CBL_ByteStoreValue
