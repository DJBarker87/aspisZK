import SDX_Join_QueryModel
import AspisR1PublicPreparation.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
open SDX_Join_Release
/- Explicit carrier projections to the coherent public-preparation producer.
   Equality of the shipped helper to this model remains OPEN, no new trust. -/
def SDX_Join_oldLive (s : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  { pool := s.pool
    deployment_domain := s.deployment_domain
    sequence := s.sequence
    next_pair_index := s.next_pair_index
    current_root := s.current_root
    frontier := s.frontier }
def SDX_Join_oldAfter (s : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index := s.next_pair_index, next_root := s.next_root, next_frontier := s.next_frontier}
def SDX_Join_oldTransition (s : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  ⟨SDX_Join_oldLive s.live_snapshot,SDX_Join_oldAfter s.candidate_afterstate⟩
def SDX_Join_oldPublic (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) :
    AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public :=
  match p with
  | .Transfer p t => .Transfer
    {pool := p.pool, deployment_domain := p.deployment_domain, anchor_sequence := p.anchor_sequence,
      anchor_root := p.anchor_root, nullifier := p.nullifier, asset_id := p.asset_id,
      recipient_commitment := p.recipient_commitment, change_commitment := p.change_commitment}
    (SDX_Join_oldTransition t)
  | .Withdrawal p t => .Withdrawal
    {pool := p.pool, deployment_domain := p.deployment_domain, anchor_sequence := p.anchor_sequence,
      anchor_root := p.anchor_root, nullifier := p.nullifier, asset_id := p.asset_id, amount := p.amount,
      destination_token_account := p.destination_token_account, change_commitment := p.change_commitment}
    (SDX_Join_oldTransition t)
def aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
    (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) :
    Result (core.result.Result (alloc.vec.Vec U8) aspis_core.state_only_prefix.r0.Error) := do
  let r ← AspisR1PublicPreparation.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes (SDX_Join_oldPublic p)
  match r with
  | .Ok bs => ok (.Ok bs)
  | .Err _ => ok (.Err .Public)
#print axioms aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes
