import R1Z.PV_DL_FinalizeParam
import R1Z.PV_CBL_ShaBitLength
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_LengthEncoding
set_option autoImplicit false

/-- Explicit big-endian suffix. Only eight byte casts are constructed. -/
def suffix (bits : U64) : Array U8 8#usize :=
  Array.make 8#usize [UScalar.cast .U8 (U64.wrapping_shr bits 56#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 48#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 40#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 32#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 24#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 16#u32),
    UScalar.cast .U8 (U64.wrapping_shr bits 8#u32),UScalar.cast .U8 bits]

theorem suffix_length (bits : U64) : (suffix bits).val.length=8 :=
  (suffix bits).property

theorem length_value (pos : Usize) (blocks : U64) :
    (PV_CBL_ShaBitLength.bitLength pos blocks).val=(8*(pos.val+64*blocks.val))%2^64 :=
  PV_CBL_ShaBitLength.value pos blocks

def finalize {S : Type} (compress : S → List U8 → Result S) (state : S)
    (blocks : U64) (buffer : Array U8 64#usize) (pos : Usize) : Result (S × List U8 × Nat) :=
  PV_DL_FinalizeParam.reference compress state buffer pos
    (suffix (PV_CBL_ShaBitLength.bitLength pos blocks))

theorem source {S : Type} (compress : S → List U8 → Result S) (state : S)
    (blocks : U64) (buffer : Array U8 64#usize) (pos : Usize) (hp : pos.val<64) :
    finalize compress state blocks buffer pos=
      PV_DL_FinalizeParam.model compress state buffer.val pos.val
        (suffix (PV_CBL_ShaBitLength.bitLength pos blocks)).val :=
  PV_DL_FinalizeParam.source compress state buffer pos _ hp

#print axioms suffix
#print axioms suffix_length
#print axioms length_value
#print axioms finalize
#print axioms source
end R1Z.PV_DL_LengthEncoding
