import PV_B3P_ProjectV3Law226
namespace PV_B3P_MetadataAudit226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

theorem transfer_metadata
    (p : aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1)
    (t : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (pool domain : Array U8 32#usize) (sequence : U64) :
    reference226.public_bytes (.Transfer
      {p with pool := pool, deployment_domain := domain, anchor_sequence := sequence} t) =
    reference226.public_bytes (.Transfer p t) := rfl

theorem withdrawal_metadata
    (p : aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1)
    (t : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1)
    (pool domain destination : Array U8 32#usize) (sequence : U64) :
    reference226.public_bytes (.Withdrawal
      {p with
        pool := pool
        deployment_domain := domain
        anchor_sequence := sequence
        destination_token_account := destination} t) =
    reference226.public_bytes (.Withdrawal p t) := rfl

def replaceTransition (s : reference226.Source)
    (f : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 →
      aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : reference226.Source :=
  match s with
  | .Transfer p t => .Transfer p (f t)
  | .Withdrawal p t => .Withdrawal p (f t)

theorem transition_metadata (s : reference226.Source) (pool domain : Array U8 32#usize)
    (sequence afterIndex : U64) (root : Array U32 8#usize) :
    reference226.public_bytes (replaceTransition s (fun t =>
      { t with
        live_snapshot := {t.live_snapshot with
          pool := pool
          deployment_domain := domain
          sequence := sequence
          current_root := root}
        candidate_afterstate := {t.candidate_afterstate with next_pair_index := afterIndex} })) =
    reference226.public_bytes s := by
  cases s <;> rfl

-- Result-value framing only; these are not side-channel or endpoint claims.
#print axioms transfer_metadata
#print axioms withdrawal_metadata
#print axioms transition_metadata
end PV_B3P_MetadataAudit226V3
