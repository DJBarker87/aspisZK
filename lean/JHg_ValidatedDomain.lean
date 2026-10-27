import JHg_AccountValues
import JFs_PublicValidation
set_option autoImplicit false
namespace AspisR1.JHg_ValidatedDomain
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
/-- Corrected field-copy diagnostic. This is not a reached authentication or
reconstruction result. Native terminal validation is reused without reduction. -/
def snapshot := {JFt_SnapshotValue.value with deployment_domain:=JHg_AccountValues.domain}
def common := {JFs_PublicValue.common with lane_transition:=
  {JFs_PublicValue.common.lane_transition with live_snapshot:=snapshot}}
def value : PoolV1PairForestTerminalStatementV1 := .PrivateTransfer common JFs_PaymentValue.value

theorem same : value=JFs_PublicValue.value := by
  unfold value common snapshot
  rw [JHg_AccountValues.domain_target]
  rfl
#print axioms same

theorem source : validate_pool_v1_pair_forest_terminal_statement_v1 value=ok (.Ok ()) := by
  rw [same]
  exact JFs_PublicValidation.source
#print axioms source
end AspisR1.JHg_ValidatedDomain
