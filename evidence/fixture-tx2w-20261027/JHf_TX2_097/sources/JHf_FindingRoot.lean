import JHf_TX2MasterField
import JHf_ValidationRejection
import JHf_Scan
import JHf_OffsetModel
set_option autoImplicit false
namespace AspisR1.JHf_FindingRoot
open Aeneas Aeneas.Std Result

/-- Unconditional local computed facts. This supplies neither an accepted
native pair nor non-vacuity of the deployed headline hypotheses. -/
theorem computed :
    JHf_DomainBytes.master≠JFt_SnapshotValue.value.deployment_domain ∧
    JHf_Scan.source JHb_Header.account=ok (.Ok JHd_ScanValue.value) ∧
    AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1
      JHf_ReconstructedStatement.value=ok (.Err .DeploymentBindingMismatch) :=
  ⟨JHf_DomainBytes.mismatch,JHf_Scan.real,JHf_ValidationRejection.source⟩
#print axioms computed
end AspisR1.JHf_FindingRoot
