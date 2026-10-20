import AspisR1CanonicalFieldStream.Types
import CuSavingsCanonicalDotsSources
import ExtractedFirstCallerReachability
set_option autoImplicit false
namespace AspisR1CanonicalDots
open Aeneas Aeneas.Std Result
/-- Same admitted source result mapper already used by the complete original
source caller interpretation, not an opaque map_err equivalence premise. -/
abbrev core.result.Result.map_err := @AspisR1PublicPreparation.core.result.Result.map_err
/-- Exact shared source field read on the nominal input-parser carrier, with
coordinate-only transport into the identical dot field carrier. -/
def weights.field (bytes : Slice U8) (index : Usize) : Result field.wide_exact.WideExact := do
  let value ← AspisR1CanonicalInputs.weights.field bytes index
  .ok (AspisR1.CuSavingsCanonicalDotsSources.inputToDot value)
#print axioms weights.field
end AspisR1CanonicalDots
