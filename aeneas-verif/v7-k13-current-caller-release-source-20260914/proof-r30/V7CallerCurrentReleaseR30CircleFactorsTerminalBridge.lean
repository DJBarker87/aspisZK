import V7CallerCurrentReleaseR30CircleFactorsCanonical
import V7CallerCurrentReleaseR26AcceptedTerminalEndToEnd

/-!
# Current circle factors at the terminal tensor interface

The current source proof uses an elementwise canonicality predicate to avoid
replaying terminal imports.  This file identifies it with the existing tensor
fold predicate at the one interface where the terminal theorem consumes it.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7CallerCurrentReleaseR26

namespace V7CallerCurrentReleaseR30CircleFactorsTerminalBridge

open V7CallerCurrentReleaseR26AcceptedCircleOrigin
open V7CallerCurrentReleaseR30CircleAccumulator
open V7CallerCurrentReleaseR30CircleFactorsCanonical

theorem AcceptedCircleStep.tensor_factors_canonical
    {Fields : Type} {fieldsInst : v6_onefold.V6FixedFieldStream Fields}
    {state next : CircleState Fields}
    {iterNext : core.ops.range.Range Std.I32}
    (step : AcceptedCircleStep fieldsInst state next iterNext) :
    V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList
      step.factors.val := by
  simpa only [CanonicalFactors,
    V7CallerCurrentReleaseR26TensorFoldSemantics.CanonicalList] using
    V7CallerCurrentReleaseR30CircleFactorsCanonical.AcceptedCircleStep.factors_canonical
      step

#print axioms AcceptedCircleStep.tensor_factors_canonical

end V7CallerCurrentReleaseR30CircleFactorsTerminalBridge
