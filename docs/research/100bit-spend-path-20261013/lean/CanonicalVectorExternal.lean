import CanonicalVectorTypes
import AspisR1CanonicalDots.Funs
set_option autoImplicit false
namespace AspisR1CanonicalDots
open Aeneas Aeneas.Std Result
class VectorCommon where
  decode : Slice U8→Result (Option field.QM31)
  claimScalar : Usize→Result field.QM31
abbrev field.QM31.from_le_bytes [VectorCommon] := VectorCommon.decode
abbrev claim_scalar [VectorCommon] := VectorCommon.claimScalar
def core.result.Result.map_err
  {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F) (self : core.result.Result T E) (op : O) :
  Result (core.result.Result T F)
  := do
  match self with
  | core.result.Result.Ok t => ok (core.result.Result.Ok t)
  | core.result.Result.Err e =>
    let t ← opsfunctionFnOnceOTupleEFInst.call_once op e
    ok (core.result.Result.Err t)

#print axioms VectorCommon
end AspisR1CanonicalDots
