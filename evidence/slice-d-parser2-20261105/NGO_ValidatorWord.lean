import NGO_ValidatorErrors
import AeneasWordCodec
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_ValidatorWord
/-- The retained natural scan reads the same four little-endian bytes as
the emitted source parser, including the full u32 range. -/
theorem le32 (a b c d : U8) :
    NFU_Retarget.LPl_Kit_Bytes.le32 [a,b,c,d]=
      (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])).val := by
  rw [AspisV8R19.SamplerWordBridge.four_bytes]
  simp [NFU_Retarget.LPl_Kit_Bytes.le32]
  ring
#print axioms le32
end NGO_ValidatorWord
