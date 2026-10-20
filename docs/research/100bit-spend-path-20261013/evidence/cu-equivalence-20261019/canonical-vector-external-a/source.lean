import CanonicalVectorTypes
import AspisR1CanonicalDots.Funs
import AspisR1RhoAccumulatorNew.FunsExternal
set_option autoImplicit false
namespace AspisR1CanonicalDots
open Aeneas Aeneas.Std Result
class VectorCommon where
  decode : Slice U8→Result (Option field.QM31)
  claimScalar : Usize→Result field.QM31
abbrev field.QM31.from_le_bytes [VectorCommon] := VectorCommon.decode
abbrev claim_scalar [VectorCommon] := VectorCommon.claimScalar
abbrev core.result.Result.map_err := @AspisR1PublicPreparation.core.result.Result.map_err
#print axioms VectorCommon
end AspisR1CanonicalDots
