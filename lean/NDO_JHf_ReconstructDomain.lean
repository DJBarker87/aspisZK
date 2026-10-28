import ExtractedAdapterReconstructSuccess
import NDO_JHf_DomainBytes
set_option autoImplicit false
namespace AspisR1.JHf_ReconstructDomain
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct r1_pool_adapter
open aspis_statement.pool_v1.pair_forest_terminal

def domain : PoolV1PairForestTerminalStatementV1 → Array U8 32#usize
  | .PrivateTransfer common _=>common.lane_transition.live_snapshot.deployment_domain
  | .Withdrawal common _=>common.lane_transition.live_snapshot.deployment_domain

theorem preserves (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts)
    (candidate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1)
    (run : reconstruct_asq8_statement request a candidate=ok (.Ok out)) :
    domain out=a.live_snapshot.deployment_domain := by
  have h:=AdapterReconstructSuccess.reconstruct_success request a candidate out run
  rw [h.2.2.1]
  cases request.«public» <;> rfl
#print axioms preserves

theorem cannot_match (request : PoolV1PairForestTerminalRequestV1)
    (a : AuthenticatedAsq8Accounts)
    (candidate : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1)
    (faithful : a.live_snapshot.deployment_domain=JHf_DomainBytes.master)
    (matching : domain out=JFt_SnapshotValue.value.deployment_domain) :
    reconstruct_asq8_statement request a candidate≠ok (.Ok out) := by
  intro run
  have h:=(preserves request a candidate out run).trans faithful
  exact JHf_DomainBytes.mismatch (h.symm.trans matching)
#print axioms cannot_match
end AspisR1.JHf_ReconstructDomain
