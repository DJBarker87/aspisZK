import AspisR1CanonicalFieldStream.Types
import CuSavingsCanonicalDotsSources
set_option autoImplicit false
namespace AspisR1CanonicalDots
open Aeneas Aeneas.Std Result
/-- Same admitted source result mapper already used by the complete original
source caller interpretation, not an opaque map_err equivalence premise. -/
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
/-- Exact shared source field read on the nominal input-parser carrier, with
coordinate-only transport into the identical dot field carrier. -/
def weights.field (bytes : Slice U8) (index : Usize) : Result field.wide_exact.WideExact := do
  let value ← AspisR1CanonicalInputs.weights.field bytes index
  .ok (AspisR1.CuSavingsCanonicalDotsSources.inputToDot value)
#print axioms weights.field
end AspisR1CanonicalDots
