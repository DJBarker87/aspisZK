import ExtractedAdapterTransferBindings
import ExtractedAdapterWithdrawalBindings

/-! R20 pure field-copy agreement. `sameSnapshot` is the audited account-shell
boundary: it is not proved for AccountInfo here. `encode` may be instantiated
with either actual deterministic serializer; no totality/injectivity claim.
The Pool field map below is checked against pair_forest.rs:1473–1502. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1AdapterReconstruct.R20PoolStatementAgreement
open aspis_statement.pool_v1.pair_forest_terminal
open aspis_statement.pool_v1.pair_terminal
open aspis_statement.pool_v1.payment_relation
open r1_pool_adapter

def poolCommon (a : AuthenticatedAsq8Accounts)
    (candidate : PoolV1PairVerifiedAfterstateV1) : PoolV1PairForestTerminalCommonV1 :=
  { master_account := a.master_account
    checkpoint_account := a.checkpoint_account
    selected_lane_account := a.selected_lane_account
    output_lane := a.selected_lane.lane_id
    checkpoint_sequence := a.checkpoint.checkpoint_sequence
    historical_global_anchor := a.checkpoint.global_root
    lane_transition := {
      live_snapshot := {
        pool := a.master_account
        deployment_domain := a.master.identity.deployment_domain
        sequence := a.selected_lane.tree.next_leaf_index
        next_pair_index := a.selected_lane.tree.next_leaf_index
        current_root := a.selected_lane.tree.root
        frontier := a.selected_lane.tree.frontier }
      candidate_afterstate := candidate } }

def sameSnapshot (a : AuthenticatedAsq8Accounts) : Prop :=
  a.live_snapshot = (poolCommon a {
    next_pair_index := a.selected_lane.tree.next_leaf_index
    next_root := a.selected_lane.tree.root
    next_frontier := a.selected_lane.tree.frontier }).lane_transition.live_snapshot

theorem common_agreement (a : AuthenticatedAsq8Accounts)
    (candidate : PoolV1PairVerifiedAfterstateV1) (hs : sameSnapshot a) :
    AdapterReconstructSuccess.common a candidate = poolCommon a candidate := by
  change a.live_snapshot = _ at hs
  simp only [AdapterReconstructSuccess.common, poolCommon, hs]

theorem transfer_serialization_agreement {α : Type}
    (encode : PoolV1PairForestTerminalStatementV1 → α)
    (request : PoolV1PairForestTerminalRequestV1) (a : AuthenticatedAsq8Accounts)
    (candidate : PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1) (p : PoolV1PrivateTransferPublicV1)
    (hp : request.«public» = .PrivateTransfer p)
    (hr : reconstruct_asq8_statement request a candidate = ok (.Ok out))
    (hs : sameSnapshot a) :
    encode out = encode (.PrivateTransfer (poolCommon a candidate) p) := by
  obtain ⟨he, _, _⟩ := TransferBindings.reconstruct_transfer_payload request a candidate out p hp hr
  rw [he, common_agreement a candidate hs]

theorem withdrawal_serialization_agreement {α : Type}
    (encode : PoolV1PairForestTerminalStatementV1 → α)
    (request : PoolV1PairForestTerminalRequestV1) (a : AuthenticatedAsq8Accounts)
    (candidate : PoolV1PairVerifiedAfterstateV1)
    (out : PoolV1PairForestTerminalStatementV1) (p : PoolV1WithdrawalPublicV1)
    (hp : request.«public» = .Withdrawal p)
    (hr : reconstruct_asq8_statement request a candidate = ok (.Ok out))
    (hs : sameSnapshot a) :
    encode out = encode (.Withdrawal (poolCommon a candidate) p) := by
  obtain ⟨_, _, he, _⟩ := AdapterReconstructSuccess.reconstruct_success request a candidate out hr
  have he' : out = .Withdrawal (AdapterReconstructSuccess.common a candidate) p := by
    simpa only [hp, AdapterReconstructSuccess.statement] using he
  rw [he', common_agreement a candidate hs]

#print axioms common_agreement
#print axioms transfer_serialization_agreement
#print axioms withdrawal_serialization_agreement
end AspisR1AdapterReconstruct.R20PoolStatementAgreement
