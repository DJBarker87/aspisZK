import CurrentClaimScalarBody
import ClaimDotConcreteAdapterV1
import S5QRaw.EbyKPushDecodedProductUpdateV1
set_option autoImplicit false
open Lean Elab Command in
run_elab do
  let env ← getEnv
  for (name, _) in env.constants.toList do
    if ("AspisR1EbyKPushDecodedProductUpdate".isPrefixOf name.toString ||
        "AspisR1FinishDotSourceABI".isPrefixOf name.toString ||
        "R22RawQmProductResidues".isPrefixOf name.toString) then
      logInfo m!"{name}"
#print AspisR1QRawGeneratedPushConnectionV2.sourceRawFn
#print axioms AspisR1CurrentPreparedClaim.ClaimScalar.body_eq_source
