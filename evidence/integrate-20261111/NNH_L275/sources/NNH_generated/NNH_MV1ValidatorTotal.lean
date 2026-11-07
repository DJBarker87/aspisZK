import NNH_MResultTotal
import NJI_V1Models
set_option autoImplicit false
noncomputable section
namespace NNH_MV1ValidatorTotal
open Aeneas Aeneas.Std Result NNH_MResultTotal

theorem registry (r : NJI_V1Carrier.R) : Total (NJI_V1Models.registry r) := by
 unfold NJI_V1Models.registry
 repeat' first | exact pure _ | split

theorem entry (r : NJI_V1Carrier.E) : Total (NJI_V1Models.entry r) := by
 unfold NJI_V1Models.entry
 repeat' first | exact pure _ | split

theorem status (v : U8) : Total
 (NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1.Insts.CoreConvertTryFromU8PoolV1VerifierRegistryFormatError.try_from v) := by
 unfold NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1.Insts.CoreConvertTryFromU8PoolV1VerifierRegistryFormatError.try_from
 repeat' first | exact pure _ | split

#print axioms registry
#print axioms entry
#print axioms status
end NNH_MV1ValidatorTotal
end
