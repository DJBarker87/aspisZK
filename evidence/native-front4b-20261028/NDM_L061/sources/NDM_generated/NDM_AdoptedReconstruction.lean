import NDM_CohortReconstruction
import NDM_CohortStatement
import NDM_CohortCommon
set_option autoImplicit false
namespace NDM_AdoptedReconstruction
open Aeneas Aeneas.Std Result AdapterRw
open AspisR1.JHf_Carrier

/-- Control normalization of the existing op52 source selection, including
 its actual carrier/error conversion. No replacement dictionary is installed. -/
theorem selected (request : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1)
 (a : r1_pool_adapter.AuthenticatedAsq8Accounts) (c : NDM_CommonCarrier.Candidate) :
 AspisR1.JHf_ReconstructionSlot.source request a c =
 (do let raw ← NDM_CohortReconstruction.direct (toRequest request)
       (toAuthenticatedAsq8Accounts a) (toPoolV1PairVerifiedAfterstateV1 c)
     ok (NDM_CohortStatement.transport raw)) := by
 unfold AspisR1.JHf_ReconstructionSlot.source
 rw [NDM_CohortReconstruction.control]
 rfl

#print axioms selected
end NDM_AdoptedReconstruction
