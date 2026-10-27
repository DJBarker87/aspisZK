import CurrentClaimScalarBody
import ClaimDotConcreteAdapterV1
import S5QRaw.EbyKPushDecodedProductUpdateV1
set_option autoImplicit false
open Lean Elab Command in
run_elab do
  let env ← getEnv
  for entry in env.constants.toList do
    let declName := entry.1
    if ("AspisR1EbyKPushDecodedProductUpdate".isPrefixOf declName.toString ||
        "AspisR1FinishDotSourceABI".isPrefixOf declName.toString ||
        "R22RawQmProductResidues".isPrefixOf declName.toString) then
      logInfo m!"{declName}"
#print AspisR1QRawGeneratedPushConnectionV2.sourceRawFn
#print axioms AspisR1CurrentPreparedClaim.ClaimScalar.body_eq_source
