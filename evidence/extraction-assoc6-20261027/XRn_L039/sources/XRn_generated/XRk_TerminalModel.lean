import XRk_MaskModel
import FIq_Native14
open Aeneas Aeneas.Std Result ControlFlow Error
open XRk_Release XRk_FieldExternal
/- Read-only reuse of the coherent complete native terminal (FIq_Terminal),
   with explicit release/cohort carriers. This does not prove its source P6
   or claim that the old public carrier is the shipped physical public bytes. -/
def XRk_nativeLive (s : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  { pool := s.pool
    deployment_domain := s.deployment_domain
    sequence := s.sequence
    next_pair_index := s.next_pair_index
    current_root := s.current_root
    frontier := s.frontier }
def XRk_nativeAfter (s : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    FIq_Native.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index := s.next_pair_index, next_root := s.next_root, next_frontier := s.next_frontier}
def XRk_nativeTransition (s : aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    FIq_Native.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  ⟨XRk_nativeLive s.live_snapshot,XRk_nativeAfter s.candidate_afterstate⟩
def XRk_nativePublic (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) :
    FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public :=
  match p with
  | .Transfer p t => .Transfer
    {pool := p.pool, deployment_domain := p.deployment_domain, anchor_sequence := p.anchor_sequence,
      anchor_root := p.anchor_root, nullifier := p.nullifier, asset_id := p.asset_id,
      recipient_commitment := p.recipient_commitment, change_commitment := p.change_commitment}
    (XRk_nativeTransition t)
  | .Withdrawal p t => .Withdrawal
    {pool := p.pool, deployment_domain := p.deployment_domain, anchor_sequence := p.anchor_sequence,
      anchor_root := p.anchor_root, nullifier := p.nullifier, asset_id := p.asset_id, amount := p.amount,
      destination_token_account := p.destination_token_account, change_commitment := p.change_commitment}
    (XRk_nativeTransition t)
def XRk_nativeQ (q : aspis_core.field.QM31) : FIq_Native.field.QM31 := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def XRk_releaseQ (q : FIq_Native.field.QM31) : aspis_core.field.QM31 := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def XRk_mapArray {T U : Type} {N : Usize} (f : T → U) (a : Array T N) : Array U N :=
  ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
def XRk_oldChallenges (c : aspis_core.state_only_prefix.r0.Challenges) :
    FIq_Native.state_only_prefix.r0.Challenges :=
  {lambda := XRk_nativeQ c.lambda, chi := XRk_nativeQ c.chi, theta := XRk_nativeQ c.theta,
   zc := XRk_mapArray XRk_nativeQ c.zc, mu := XRk_nativeQ c.mu, eta := XRk_nativeQ c.eta}
def XRk_newError : FIq_Native.state_only_prefix.r0.Error → aspis_core.state_only_prefix.r0.Error
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
  let r ← FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31 (XRk_nativePublic p)
    (XRk_mapArray (XRk_mapArray XRk_nativeQ) claims)
    (XRk_mapArray XRk_nativeQ alpha) (XRk_oldChallenges c)
  match r with
  | .Ok q => ok (.Ok (XRk_releaseQ q))
  | .Err e => ok (.Err (XRk_newError e))
#print axioms aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
