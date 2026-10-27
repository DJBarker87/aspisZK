import JHf_DomainBytes
import JFs_PublicEncoders
import JFs_PublicComparisons
set_option autoImplicit false
namespace AspisR1.JHf_ReconstructedStatement
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
/-- The source field-copy result if all other returned fields match the
retained target and the live domain is faithfully decoded from the master.
This is a diagnostic value, not a successful authentication assumption. -/
def snapshot := {JFt_SnapshotValue.value with deployment_domain:=JHf_DomainBytes.master}
def common := {JFs_PublicValue.common with lane_transition:=
  {JFs_PublicValue.common.lane_transition with live_snapshot:=snapshot}}
def value : PoolV1PairForestTerminalStatementV1 := .PrivateTransfer common JFs_PaymentValue.value

theorem domain_compare : core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
    JFs_PaymentValue.common.deployment_domain snapshot.deployment_domain=ok true := by rfl
#print axioms domain_compare

theorem distinct : value≠JFs_PublicValue.value := by
  intro same
  have h:=congrArg (fun s : PoolV1PairForestTerminalStatementV1 => match s with
    | .PrivateTransfer c _=>c.lane_transition.live_snapshot.deployment_domain
    | .Withdrawal c _=>c.lane_transition.live_snapshot.deployment_domain) same
  exact JHf_DomainBytes.mismatch h
#print axioms distinct
end AspisR1.JHf_ReconstructedStatement
