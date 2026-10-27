import LPi_WriterValues
set_option autoImplicit false
namespace AspisR1.LPi_ByteWord
open Aeneas Aeneas.Std Result

theorem source (x : U32) :
    OraclePortCkptAbi2Extracted.aspis_core.field.M31.to_le_bytes x =
      ok (core.num.U32.to_le_bytes x) := rfl

#print axioms source
end AspisR1.LPi_ByteWord
