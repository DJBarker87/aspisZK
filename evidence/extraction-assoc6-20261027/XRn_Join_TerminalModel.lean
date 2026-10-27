import XRn_Join_MaskModel
import FIq_Native14
open Aeneas Aeneas.Std Result ControlFlow Error
open XRn_Join_Release XRn_Join_FieldExternal
/- Read-only reuse of the coherent complete native terminal (FIq_Terminal),
   with explicit release/cohort carriers. This does not prove its source P6
   or claim that the old public carrier is the shipped physical public bytes. -/
def XRn_Join_nativeLive (s : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  { pool := s.pool
    deployment_domain := s.deployment_domain
    sequence := s.sequence
    next_pair_index := s.next_pair_index
    current_root := s.current_root
    frontier := s.frontier }
def XRn_Join_nativeAfter (s : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    FIq_Native.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index := s.next_pair_index, next_root := s.next_root, next_frontier := s.next_frontier}
def XRn_Join_nativeTransition (s : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  ⟨XRn_Join_nativeLive s.live_snapshot,XRn_Join_nativeAfter s.candidate_afterstate⟩
def XRn_Join_nativePublic (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) :
    FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public :=
  match p with
  | .Transfer p t => .Transfer
    {pool := p.pool, deployment_domain := p.deployment_domain, anchor_sequence := p.anchor_sequence,
      anchor_root := p.anchor_root, nullifier := p.nullifier, asset_id := p.asset_id,
      recipient_commitment := p.recipient_commitment, change_commitment := p.change_commitment}
    (XRn_Join_nativeTransition t)
  | .Withdrawal p t => .Withdrawal
    {pool := p.pool, deployment_domain := p.deployment_domain, anchor_sequence := p.anchor_sequence,
      anchor_root := p.anchor_root, nullifier := p.nullifier, asset_id := p.asset_id, amount := p.amount,
      destination_token_account := p.destination_token_account, change_commitment := p.change_commitment}
    (XRn_Join_nativeTransition t)
def XRn_Join_nativeQ (q : aspis_core.field.QM31) : FIq_Native.field.QM31 := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def XRn_Join_releaseQ (q : FIq_Native.field.QM31) : aspis_core.field.QM31 := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def XRn_Join_mapArray {T U : Type} {N : Usize} (f : T → U) (a : Array T N) : Array U N :=
  ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
def XRn_Join_oldChallenges (c : aspis_core.state_only_prefix.r0.Challenges) :
    FIq_Native.state_only_prefix.r0.Challenges :=
  {lambda := XRn_Join_nativeQ c.lambda, chi := XRn_Join_nativeQ c.chi, theta := XRn_Join_nativeQ c.theta,
   zc := XRn_Join_mapArray XRn_Join_nativeQ c.zc, mu := XRn_Join_nativeQ c.mu, eta := XRn_Join_nativeQ c.eta}
def XRn_Join_newError : FIq_Native.state_only_prefix.r0.Error → aspis_core.state_only_prefix.r0.Error
  | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow | .Tag a => .Tag a | .Length a => .Length a
  | .NonCanonical a b => .NonCanonical a b | .Boundary a => .Boundary a
  | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes | .Public => .Public
noncomputable def aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
    (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (alpha : Array aspis_core.field.QM31 10#usize) (c : aspis_core.state_only_prefix.r0.Challenges) :
    Result (core.result.Result aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error) := do
  let r ← FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31 (XRn_Join_nativePublic p)
    (XRn_Join_mapArray (XRn_Join_mapArray XRn_Join_nativeQ) claims)
    (XRn_Join_mapArray XRn_Join_nativeQ alpha) (XRn_Join_oldChallenges c)
  match r with
  | .Ok q => ok (.Ok (XRn_Join_releaseQ q))
  | .Err e => ok (.Err (XRn_Join_newError e))
#print axioms aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
