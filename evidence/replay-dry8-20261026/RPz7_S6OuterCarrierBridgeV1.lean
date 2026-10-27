import S6FullForestEncoderNamedTypesV1
import RPz7_S6NativeLateCodecV1
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisS6OuterCarrierBridge

def toPoolV1TransitionKind (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind) : AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind :=
  match value with
  | .PrivateTransfer => AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
  | .Withdrawal => AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal

def fromPoolV1TransitionKind (value : AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind :=
  match value with
  | .PrivateTransfer => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
  | .Withdrawal => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal

@[simp] theorem from_toPoolV1TransitionKind (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind) : fromPoolV1TransitionKind (toPoolV1TransitionKind value)=value := by
  cases value <;> simp only [toPoolV1TransitionKind,fromPoolV1TransitionKind]
  all_goals rfl

@[simp] theorem to_fromPoolV1TransitionKind (value : AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind) : toPoolV1TransitionKind (fromPoolV1TransitionKind value)=value := by
  cases value <;> simp only [toPoolV1TransitionKind,fromPoolV1TransitionKind]
  all_goals rfl

def equivPoolV1TransitionKind : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.historical_anchor.PoolV1TransitionKind ≃ AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind where
  toFun := toPoolV1TransitionKind
  invFun := fromPoolV1TransitionKind
  left_inv := from_toPoolV1TransitionKind
  right_inv := to_fromPoolV1TransitionKind

#print axioms equivPoolV1TransitionKind

def toPoolV1TreeError (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError) : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError :=
  match value with
  | .TreeFull => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.TreeFull
  | .InsufficientCapacity => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.InsufficientCapacity
  | .IndexOutOfRange => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.IndexOutOfRange
  | .RootMismatch => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.RootMismatch
  | .NonCanonicalFrontier => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalFrontier
  | .WrongLength => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongLength
  | .WrongMagic => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongMagic
  | .WrongVersion => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongVersion
  | .WrongDepth => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongDepth
  | .WrongTreeHash => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongTreeHash
  | .WrongDigestEncoding => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.WrongDigestEncoding
  | .NonCanonicalDigest => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalDigest
  | .NonZeroReserved => AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError.NonZeroReserved

def fromPoolV1TreeError (value : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError :=
  match value with
  | .TreeFull => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.TreeFull
  | .InsufficientCapacity => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.InsufficientCapacity
  | .IndexOutOfRange => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.IndexOutOfRange
  | .RootMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.RootMismatch
  | .NonCanonicalFrontier => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalFrontier
  | .WrongLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.WrongLength
  | .WrongMagic => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.WrongMagic
  | .WrongVersion => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.WrongVersion
  | .WrongDepth => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.WrongDepth
  | .WrongTreeHash => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.WrongTreeHash
  | .WrongDigestEncoding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.WrongDigestEncoding
  | .NonCanonicalDigest => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.NonCanonicalDigest
  | .NonZeroReserved => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError.NonZeroReserved

@[simp] theorem from_toPoolV1TreeError (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError) : fromPoolV1TreeError (toPoolV1TreeError value)=value := by
  cases value <;> simp only [toPoolV1TreeError,fromPoolV1TreeError,from_toPoolV1TransitionKind]
  all_goals rfl

@[simp] theorem to_fromPoolV1TreeError (value : AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError) : toPoolV1TreeError (fromPoolV1TreeError value)=value := by
  cases value <;> simp only [toPoolV1TreeError,fromPoolV1TreeError,to_fromPoolV1TransitionKind]
  all_goals rfl

def equivPoolV1TreeError : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.incremental_merkle.PoolV1TreeError ≃ AspisR1TerminalDecoder.pool_v1.incremental_merkle.PoolV1TreeError where
  toFun := toPoolV1TreeError
  invFun := fromPoolV1TreeError
  left_inv := from_toPoolV1TreeError
  right_inv := to_fromPoolV1TreeError

#print axioms equivPoolV1TreeError

def toPoolV1PairForestAccountErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 :=
  match value with
  | .WrongLength => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongLength
  | .WrongMagic => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongMagic
  | .WrongVersion => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongVersion
  | .WrongLaneCount => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongLaneCount
  | .WrongDigestEncoding => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongDigestEncoding
  | .WrongDepth => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongDepth
  | .WrongFormatBinding => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongFormatBinding
  | .NonZeroReserved => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.NonZeroReserved
  | .ZeroRequiredBinding => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.ZeroRequiredBinding
  | .InvalidBoolean => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidBoolean
  | .InvalidMasterState => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidMasterState
  | .InvalidLane => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidLane
  | .LaneMasterMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.LaneMasterMismatch
  | .LaneOrderMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.LaneOrderMismatch
  | .LaneSequenceDecreased => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.LaneSequenceDecreased
  | .DuplicateCheckpoint => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.DuplicateCheckpoint
  | .CheckpointSequenceOverflow => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.CheckpointSequenceOverflow
  | .NonCanonicalDigest => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.NonCanonicalDigest
  | .Identity => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.Identity
  | .Policy => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.Policy
  | .Tree x0 => AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.Tree (toPoolV1TreeError (x0))

def fromPoolV1PairForestAccountErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 :=
  match value with
  | .WrongLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongLength
  | .WrongMagic => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongMagic
  | .WrongVersion => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongVersion
  | .WrongLaneCount => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongLaneCount
  | .WrongDigestEncoding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongDigestEncoding
  | .WrongDepth => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongDepth
  | .WrongFormatBinding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.WrongFormatBinding
  | .NonZeroReserved => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.NonZeroReserved
  | .ZeroRequiredBinding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.ZeroRequiredBinding
  | .InvalidBoolean => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidBoolean
  | .InvalidMasterState => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidMasterState
  | .InvalidLane => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.InvalidLane
  | .LaneMasterMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.LaneMasterMismatch
  | .LaneOrderMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.LaneOrderMismatch
  | .LaneSequenceDecreased => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.LaneSequenceDecreased
  | .DuplicateCheckpoint => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.DuplicateCheckpoint
  | .CheckpointSequenceOverflow => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.CheckpointSequenceOverflow
  | .NonCanonicalDigest => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.NonCanonicalDigest
  | .Identity => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.Identity
  | .Policy => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.Policy
  | .Tree x0 => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1.Tree (fromPoolV1TreeError (x0))

@[simp] theorem from_toPoolV1PairForestAccountErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : fromPoolV1PairForestAccountErrorV1 (toPoolV1PairForestAccountErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairForestAccountErrorV1,fromPoolV1PairForestAccountErrorV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairForestAccountErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : toPoolV1PairForestAccountErrorV1 (fromPoolV1PairForestAccountErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairForestAccountErrorV1,fromPoolV1PairForestAccountErrorV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError]
  all_goals rfl

def equivPoolV1PairForestAccountErrorV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 where
  toFun := toPoolV1PairForestAccountErrorV1
  invFun := fromPoolV1PairForestAccountErrorV1
  left_inv := from_toPoolV1PairForestAccountErrorV1
  right_inv := to_fromPoolV1PairForestAccountErrorV1

#print axioms equivPoolV1PairForestAccountErrorV1

def toPoolV1PairLiveSnapshotV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,sequence:=value.sequence,next_pair_index:=value.next_pair_index,current_root:=value.current_root,frontier:=value.frontier}

def fromPoolV1PairLiveSnapshotV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,sequence:=value.sequence,next_pair_index:=value.next_pair_index,current_root:=value.current_root,frontier:=value.frontier}

@[simp] theorem from_toPoolV1PairLiveSnapshotV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : fromPoolV1PairLiveSnapshotV1 (toPoolV1PairLiveSnapshotV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLiveSnapshotV1,fromPoolV1PairLiveSnapshotV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairLiveSnapshotV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : toPoolV1PairLiveSnapshotV1 (fromPoolV1PairLiveSnapshotV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLiveSnapshotV1,fromPoolV1PairLiveSnapshotV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1]
  all_goals rfl

def equivPoolV1PairLiveSnapshotV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 where
  toFun := toPoolV1PairLiveSnapshotV1
  invFun := fromPoolV1PairLiveSnapshotV1
  left_inv := from_toPoolV1PairLiveSnapshotV1
  right_inv := to_fromPoolV1PairLiveSnapshotV1

#print axioms equivPoolV1PairLiveSnapshotV1

def toPoolV1PairVerifiedAfterstateV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=value.next_pair_index,next_root:=value.next_root,next_frontier:=value.next_frontier}

def fromPoolV1PairVerifiedAfterstateV1 (value : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=value.next_pair_index,next_root:=value.next_root,next_frontier:=value.next_frontier}

@[simp] theorem from_toPoolV1PairVerifiedAfterstateV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : fromPoolV1PairVerifiedAfterstateV1 (toPoolV1PairVerifiedAfterstateV1 value)=value := by
  cases value <;> simp only [toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairVerifiedAfterstateV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairVerifiedAfterstateV1 (value : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : toPoolV1PairVerifiedAfterstateV1 (fromPoolV1PairVerifiedAfterstateV1 value)=value := by
  cases value <;> simp only [toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1]
  all_goals rfl

def equivPoolV1PairVerifiedAfterstateV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 where
  toFun := toPoolV1PairVerifiedAfterstateV1
  invFun := fromPoolV1PairVerifiedAfterstateV1
  left_inv := from_toPoolV1PairVerifiedAfterstateV1
  right_inv := to_fromPoolV1PairVerifiedAfterstateV1

#print axioms equivPoolV1PairVerifiedAfterstateV1

def toPoolV1PairLatePublicStatementV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=toPoolV1PairLiveSnapshotV1 (value.live_snapshot),candidate_afterstate:=toPoolV1PairVerifiedAfterstateV1 (value.candidate_afterstate)}

def fromPoolV1PairLatePublicStatementV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=fromPoolV1PairLiveSnapshotV1 (value.live_snapshot),candidate_afterstate:=fromPoolV1PairVerifiedAfterstateV1 (value.candidate_afterstate)}

@[simp] theorem from_toPoolV1PairLatePublicStatementV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : fromPoolV1PairLatePublicStatementV1 (toPoolV1PairLatePublicStatementV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLatePublicStatementV1,fromPoolV1PairLatePublicStatementV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairLatePublicStatementV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : toPoolV1PairLatePublicStatementV1 (fromPoolV1PairLatePublicStatementV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLatePublicStatementV1,fromPoolV1PairLatePublicStatementV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1]
  all_goals rfl

def equivPoolV1PairLatePublicStatementV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 where
  toFun := toPoolV1PairLatePublicStatementV1
  invFun := fromPoolV1PairLatePublicStatementV1
  left_inv := from_toPoolV1PairLatePublicStatementV1
  right_inv := to_fromPoolV1PairLatePublicStatementV1

#print axioms equivPoolV1PairLatePublicStatementV1

def toPoolV1PairForestTerminalCommonV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
  {master_account:=value.master_account,checkpoint_account:=value.checkpoint_account,selected_lane_account:=value.selected_lane_account,output_lane:=value.output_lane,checkpoint_sequence:=value.checkpoint_sequence,historical_global_anchor:=value.historical_global_anchor,lane_transition:=toPoolV1PairLatePublicStatementV1 (value.lane_transition)}

def fromPoolV1PairForestTerminalCommonV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
  {master_account:=value.master_account,checkpoint_account:=value.checkpoint_account,selected_lane_account:=value.selected_lane_account,output_lane:=value.output_lane,checkpoint_sequence:=value.checkpoint_sequence,historical_global_anchor:=value.historical_global_anchor,lane_transition:=fromPoolV1PairLatePublicStatementV1 (value.lane_transition)}

@[simp] theorem from_toPoolV1PairForestTerminalCommonV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : fromPoolV1PairForestTerminalCommonV1 (toPoolV1PairForestTerminalCommonV1 value)=value := by
  cases value <;> simp only [toPoolV1PairForestTerminalCommonV1,fromPoolV1PairForestTerminalCommonV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairForestTerminalCommonV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : toPoolV1PairForestTerminalCommonV1 (fromPoolV1PairForestTerminalCommonV1 value)=value := by
  cases value <;> simp only [toPoolV1PairForestTerminalCommonV1,fromPoolV1PairForestTerminalCommonV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1]
  all_goals rfl

def equivPoolV1PairForestTerminalCommonV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 where
  toFun := toPoolV1PairForestTerminalCommonV1
  invFun := fromPoolV1PairForestTerminalCommonV1
  left_inv := from_toPoolV1PairForestTerminalCommonV1
  right_inv := to_fromPoolV1PairForestTerminalCommonV1

#print axioms equivPoolV1PairForestTerminalCommonV1

def toPoolV1WithdrawalPublicV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,amount:=value.amount,destination_token_account:=value.destination_token_account,change_commitment:=value.change_commitment}

def fromPoolV1WithdrawalPublicV1 (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,amount:=value.amount,destination_token_account:=value.destination_token_account,change_commitment:=value.change_commitment}

@[simp] theorem from_toPoolV1WithdrawalPublicV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : fromPoolV1WithdrawalPublicV1 (toPoolV1WithdrawalPublicV1 value)=value := by
  cases value <;> simp only [toPoolV1WithdrawalPublicV1,fromPoolV1WithdrawalPublicV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1PairForestTerminalCommonV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1WithdrawalPublicV1 (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : toPoolV1WithdrawalPublicV1 (fromPoolV1WithdrawalPublicV1 value)=value := by
  cases value <;> simp only [toPoolV1WithdrawalPublicV1,fromPoolV1WithdrawalPublicV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1PairForestTerminalCommonV1]
  all_goals rfl

def equivPoolV1WithdrawalPublicV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 ≃ AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 where
  toFun := toPoolV1WithdrawalPublicV1
  invFun := fromPoolV1WithdrawalPublicV1
  left_inv := from_toPoolV1WithdrawalPublicV1
  right_inv := to_fromPoolV1WithdrawalPublicV1

#print axioms equivPoolV1WithdrawalPublicV1

def toPoolV1PrivateTransferPublicV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,recipient_commitment:=value.recipient_commitment,change_commitment:=value.change_commitment}

def fromPoolV1PrivateTransferPublicV1 (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,recipient_commitment:=value.recipient_commitment,change_commitment:=value.change_commitment}

@[simp] theorem from_toPoolV1PrivateTransferPublicV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : fromPoolV1PrivateTransferPublicV1 (toPoolV1PrivateTransferPublicV1 value)=value := by
  cases value <;> simp only [toPoolV1PrivateTransferPublicV1,fromPoolV1PrivateTransferPublicV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1PairForestTerminalCommonV1,from_toPoolV1WithdrawalPublicV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PrivateTransferPublicV1 (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : toPoolV1PrivateTransferPublicV1 (fromPoolV1PrivateTransferPublicV1 value)=value := by
  cases value <;> simp only [toPoolV1PrivateTransferPublicV1,fromPoolV1PrivateTransferPublicV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1PairForestTerminalCommonV1,to_fromPoolV1WithdrawalPublicV1]
  all_goals rfl

def equivPoolV1PrivateTransferPublicV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 ≃ AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 where
  toFun := toPoolV1PrivateTransferPublicV1
  invFun := fromPoolV1PrivateTransferPublicV1
  left_inv := from_toPoolV1PrivateTransferPublicV1
  right_inv := to_fromPoolV1PrivateTransferPublicV1

#print axioms equivPoolV1PrivateTransferPublicV1

def toPoolV1PairForestTerminalStatementV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 :=
  match value with
  | .PrivateTransfer x0 x1 => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer (toPoolV1PairForestTerminalCommonV1 (x0)) (toPoolV1PrivateTransferPublicV1 (x1))
  | .Withdrawal x0 x1 => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal (toPoolV1PairForestTerminalCommonV1 (x0)) (toPoolV1WithdrawalPublicV1 (x1))

def fromPoolV1PairForestTerminalStatementV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 :=
  match value with
  | .PrivateTransfer x0 x1 => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer (fromPoolV1PairForestTerminalCommonV1 (x0)) (fromPoolV1PrivateTransferPublicV1 (x1))
  | .Withdrawal x0 x1 => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal (fromPoolV1PairForestTerminalCommonV1 (x0)) (fromPoolV1WithdrawalPublicV1 (x1))

@[simp] theorem from_toPoolV1PairForestTerminalStatementV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : fromPoolV1PairForestTerminalStatementV1 (toPoolV1PairForestTerminalStatementV1 value)=value := by
  cases value <;> simp only [toPoolV1PairForestTerminalStatementV1,fromPoolV1PairForestTerminalStatementV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1PairForestTerminalCommonV1,from_toPoolV1WithdrawalPublicV1,from_toPoolV1PrivateTransferPublicV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairForestTerminalStatementV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : toPoolV1PairForestTerminalStatementV1 (fromPoolV1PairForestTerminalStatementV1 value)=value := by
  cases value <;> simp only [toPoolV1PairForestTerminalStatementV1,fromPoolV1PairForestTerminalStatementV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1PairForestTerminalCommonV1,to_fromPoolV1WithdrawalPublicV1,to_fromPoolV1PrivateTransferPublicV1]
  all_goals rfl

def equivPoolV1PairForestTerminalStatementV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 where
  toFun := toPoolV1PairForestTerminalStatementV1
  invFun := fromPoolV1PairForestTerminalStatementV1
  left_inv := from_toPoolV1PairForestTerminalStatementV1
  right_inv := to_fromPoolV1PairForestTerminalStatementV1

#print axioms equivPoolV1PairForestTerminalStatementV1

def toPoolV1PaymentStatementFormatError (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError :=
  match value with
  | .WrongLength => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongLength
  | .WrongMagic => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongMagic
  | .WrongVersion => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongVersion
  | .WrongTransitionKind => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongTransitionKind
  | .WrongDigestEncoding => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongDigestEncoding
  | .NonZeroReserved => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved
  | .ZeroRequiredBinding => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding
  | .InvalidAnchorSequence => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence
  | .NonCanonicalDigest => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest
  | .NonCanonicalAssetId => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId
  | .InvalidWithdrawalAmount => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount
  | .InvalidDestination => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination
  | .InvalidEnvelope => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidEnvelope
  | .EnvelopeMismatch => AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.EnvelopeMismatch

def fromPoolV1PaymentStatementFormatError (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError :=
  match value with
  | .WrongLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongLength
  | .WrongMagic => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongMagic
  | .WrongVersion => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongVersion
  | .WrongTransitionKind => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongTransitionKind
  | .WrongDigestEncoding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.WrongDigestEncoding
  | .NonZeroReserved => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonZeroReserved
  | .ZeroRequiredBinding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.ZeroRequiredBinding
  | .InvalidAnchorSequence => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidAnchorSequence
  | .NonCanonicalDigest => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalDigest
  | .NonCanonicalAssetId => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.NonCanonicalAssetId
  | .InvalidWithdrawalAmount => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidWithdrawalAmount
  | .InvalidDestination => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidDestination
  | .InvalidEnvelope => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.InvalidEnvelope
  | .EnvelopeMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError.EnvelopeMismatch

@[simp] theorem from_toPoolV1PaymentStatementFormatError (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : fromPoolV1PaymentStatementFormatError (toPoolV1PaymentStatementFormatError value)=value := by
  cases value <;> simp only [toPoolV1PaymentStatementFormatError,fromPoolV1PaymentStatementFormatError,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1PairForestTerminalCommonV1,from_toPoolV1WithdrawalPublicV1,from_toPoolV1PrivateTransferPublicV1,from_toPoolV1PairForestTerminalStatementV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PaymentStatementFormatError (value : AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError) : toPoolV1PaymentStatementFormatError (fromPoolV1PaymentStatementFormatError value)=value := by
  cases value <;> simp only [toPoolV1PaymentStatementFormatError,fromPoolV1PaymentStatementFormatError,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1PairForestTerminalCommonV1,to_fromPoolV1WithdrawalPublicV1,to_fromPoolV1PrivateTransferPublicV1,to_fromPoolV1PairForestTerminalStatementV1]
  all_goals rfl

def equivPoolV1PaymentStatementFormatError : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.payment_relation.PoolV1PaymentStatementFormatError ≃ AspisR1TerminalDecoder.pool_v1.payment_relation.PoolV1PaymentStatementFormatError where
  toFun := toPoolV1PaymentStatementFormatError
  invFun := fromPoolV1PaymentStatementFormatError
  left_inv := from_toPoolV1PaymentStatementFormatError
  right_inv := to_fromPoolV1PaymentStatementFormatError

#print axioms equivPoolV1PaymentStatementFormatError

def toPoolV1PairLiveSnapshotErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 :=
  match value with
  | .WrongLength => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength
  | .WrongMagic => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongMagic
  | .WrongVersion => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongVersion
  | .WrongFormatBinding => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongFormatBinding
  | .NonZeroReserved => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved
  | .ZeroRequiredBinding => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.ZeroRequiredBinding
  | .SequenceIndexMismatch => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.SequenceIndexMismatch
  | .TreeFull => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.TreeFull
  | .NonCanonicalDigest => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonCanonicalDigest

def fromPoolV1PairLiveSnapshotErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 :=
  match value with
  | .WrongLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongLength
  | .WrongMagic => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongMagic
  | .WrongVersion => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongVersion
  | .WrongFormatBinding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.WrongFormatBinding
  | .NonZeroReserved => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonZeroReserved
  | .ZeroRequiredBinding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.ZeroRequiredBinding
  | .SequenceIndexMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.SequenceIndexMismatch
  | .TreeFull => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.TreeFull
  | .NonCanonicalDigest => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1.NonCanonicalDigest

@[simp] theorem from_toPoolV1PairLiveSnapshotErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : fromPoolV1PairLiveSnapshotErrorV1 (toPoolV1PairLiveSnapshotErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLiveSnapshotErrorV1,fromPoolV1PairLiveSnapshotErrorV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1PairForestTerminalCommonV1,from_toPoolV1WithdrawalPublicV1,from_toPoolV1PrivateTransferPublicV1,from_toPoolV1PairForestTerminalStatementV1,from_toPoolV1PaymentStatementFormatError]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairLiveSnapshotErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : toPoolV1PairLiveSnapshotErrorV1 (fromPoolV1PairLiveSnapshotErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLiveSnapshotErrorV1,fromPoolV1PairLiveSnapshotErrorV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1PairForestTerminalCommonV1,to_fromPoolV1WithdrawalPublicV1,to_fromPoolV1PrivateTransferPublicV1,to_fromPoolV1PairForestTerminalStatementV1,to_fromPoolV1PaymentStatementFormatError]
  all_goals rfl

def equivPoolV1PairLiveSnapshotErrorV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 where
  toFun := toPoolV1PairLiveSnapshotErrorV1
  invFun := fromPoolV1PairLiveSnapshotErrorV1
  left_inv := from_toPoolV1PairLiveSnapshotErrorV1
  right_inv := to_fromPoolV1PairLiveSnapshotErrorV1

#print axioms equivPoolV1PairLiveSnapshotErrorV1

def toPoolV1PairVerifierTransportErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 :=
  match value with
  | .WrongLength => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongLength
  | .WrongMagic => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongMagic
  | .WrongVersion => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongVersion
  | .WrongStatementVersion => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongStatementVersion
  | .WrongDigestEncoding => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongDigestEncoding
  | .InvalidTransitionKind => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidTransitionKind
  | .WrongSuccessCode => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongSuccessCode
  | .WrongPairFormat => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongPairFormat
  | .ZeroRequiredBinding => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.ZeroRequiredBinding
  | .InvalidProofBodyLength => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidProofBodyLength
  | .InvalidStatementPayloadLength => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidStatementPayloadLength
  | .InvalidLiveSnapshotPayloadLength => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidLiveSnapshotPayloadLength
  | .NonCanonicalOutputPair => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.NonCanonicalOutputPair
  | .InvalidAfterstateIndex => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidAfterstateIndex
  | .NonCanonicalAfterstate => AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.NonCanonicalAfterstate

def fromPoolV1PairVerifierTransportErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 :=
  match value with
  | .WrongLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongLength
  | .WrongMagic => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongMagic
  | .WrongVersion => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongVersion
  | .WrongStatementVersion => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongStatementVersion
  | .WrongDigestEncoding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongDigestEncoding
  | .InvalidTransitionKind => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidTransitionKind
  | .WrongSuccessCode => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongSuccessCode
  | .WrongPairFormat => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.WrongPairFormat
  | .ZeroRequiredBinding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.ZeroRequiredBinding
  | .InvalidProofBodyLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidProofBodyLength
  | .InvalidStatementPayloadLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidStatementPayloadLength
  | .InvalidLiveSnapshotPayloadLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidLiveSnapshotPayloadLength
  | .NonCanonicalOutputPair => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.NonCanonicalOutputPair
  | .InvalidAfterstateIndex => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.InvalidAfterstateIndex
  | .NonCanonicalAfterstate => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1.NonCanonicalAfterstate

@[simp] theorem from_toPoolV1PairVerifierTransportErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : fromPoolV1PairVerifierTransportErrorV1 (toPoolV1PairVerifierTransportErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairVerifierTransportErrorV1,fromPoolV1PairVerifierTransportErrorV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1PairForestTerminalCommonV1,from_toPoolV1WithdrawalPublicV1,from_toPoolV1PrivateTransferPublicV1,from_toPoolV1PairForestTerminalStatementV1,from_toPoolV1PaymentStatementFormatError,from_toPoolV1PairLiveSnapshotErrorV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairVerifierTransportErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : toPoolV1PairVerifierTransportErrorV1 (fromPoolV1PairVerifierTransportErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairVerifierTransportErrorV1,fromPoolV1PairVerifierTransportErrorV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1PairForestTerminalCommonV1,to_fromPoolV1WithdrawalPublicV1,to_fromPoolV1PrivateTransferPublicV1,to_fromPoolV1PairForestTerminalStatementV1,to_fromPoolV1PaymentStatementFormatError,to_fromPoolV1PairLiveSnapshotErrorV1]
  all_goals rfl

def equivPoolV1PairVerifierTransportErrorV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 where
  toFun := toPoolV1PairVerifierTransportErrorV1
  invFun := fromPoolV1PairVerifierTransportErrorV1
  left_inv := from_toPoolV1PairVerifierTransportErrorV1
  right_inv := to_fromPoolV1PairVerifierTransportErrorV1

#print axioms equivPoolV1PairVerifierTransportErrorV1

def toPoolV1PairLatePublicStatementErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 :=
  match value with
  | .WrongLength => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongLength
  | .WrongMagic => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongMagic
  | .WrongVersion => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongVersion
  | .WrongItemCount => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongItemCount
  | .WrongHeaderLength => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongHeaderLength
  | .WrongSnapshotLength => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongSnapshotLength
  | .WrongAfterstateLength => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongAfterstateLength
  | .WrongTotalLength => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongTotalLength
  | .NonZeroReserved => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved
  | .Snapshot x0 => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.Snapshot (toPoolV1PairLiveSnapshotErrorV1 (x0))
  | .Afterstate x0 => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.Afterstate (toPoolV1PairVerifierTransportErrorV1 (x0))
  | .AfterstateIndexMismatch => AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.AfterstateIndexMismatch

def fromPoolV1PairLatePublicStatementErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 :=
  match value with
  | .WrongLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongLength
  | .WrongMagic => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongMagic
  | .WrongVersion => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongVersion
  | .WrongItemCount => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongItemCount
  | .WrongHeaderLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongHeaderLength
  | .WrongSnapshotLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongSnapshotLength
  | .WrongAfterstateLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongAfterstateLength
  | .WrongTotalLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.WrongTotalLength
  | .NonZeroReserved => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.NonZeroReserved
  | .Snapshot x0 => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.Snapshot (fromPoolV1PairLiveSnapshotErrorV1 (x0))
  | .Afterstate x0 => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.Afterstate (fromPoolV1PairVerifierTransportErrorV1 (x0))
  | .AfterstateIndexMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.AfterstateIndexMismatch

@[simp] theorem from_toPoolV1PairLatePublicStatementErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : fromPoolV1PairLatePublicStatementErrorV1 (toPoolV1PairLatePublicStatementErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLatePublicStatementErrorV1,fromPoolV1PairLatePublicStatementErrorV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1PairForestTerminalCommonV1,from_toPoolV1WithdrawalPublicV1,from_toPoolV1PrivateTransferPublicV1,from_toPoolV1PairForestTerminalStatementV1,from_toPoolV1PaymentStatementFormatError,from_toPoolV1PairLiveSnapshotErrorV1,from_toPoolV1PairVerifierTransportErrorV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairLatePublicStatementErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : toPoolV1PairLatePublicStatementErrorV1 (fromPoolV1PairLatePublicStatementErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairLatePublicStatementErrorV1,fromPoolV1PairLatePublicStatementErrorV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1PairForestTerminalCommonV1,to_fromPoolV1WithdrawalPublicV1,to_fromPoolV1PrivateTransferPublicV1,to_fromPoolV1PairForestTerminalStatementV1,to_fromPoolV1PaymentStatementFormatError,to_fromPoolV1PairLiveSnapshotErrorV1,to_fromPoolV1PairVerifierTransportErrorV1]
  all_goals rfl

def equivPoolV1PairLatePublicStatementErrorV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 where
  toFun := toPoolV1PairLatePublicStatementErrorV1
  invFun := fromPoolV1PairLatePublicStatementErrorV1
  left_inv := from_toPoolV1PairLatePublicStatementErrorV1
  right_inv := to_fromPoolV1PairLatePublicStatementErrorV1

#print axioms equivPoolV1PairLatePublicStatementErrorV1

def toPoolV1PairForestTerminalFormatErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 :=
  match value with
  | .WrongLength => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength
  | .WrongMagic => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongMagic
  | .WrongVersion => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongVersion
  | .WrongDigestEncoding => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding
  | .InvalidTransitionKind => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.InvalidTransitionKind
  | .InvalidOutputLane => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.InvalidOutputLane
  | .NonZeroBinding => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding
  | .NonCanonicalDigest => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonCanonicalDigest
  | .OutputLaneMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch
  | .MasterBindingMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch
  | .DeploymentBindingMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.DeploymentBindingMismatch
  | .HistoricalAnchorMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.HistoricalAnchorMismatch
  | .CheckpointBindingMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CheckpointBindingMismatch
  | .SelectedLaneBindingMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.SelectedLaneBindingMismatch
  | .LiveSnapshotMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.LiveSnapshotMismatch
  | .CandidateAfterstateMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CandidateAfterstateMismatch
  | .ResultBindingMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.ResultBindingMismatch
  | .WithdrawalDestinationMismatch => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WithdrawalDestinationMismatch
  | .Payment x0 => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Payment (toPoolV1PaymentStatementFormatError (x0))
  | .LaneTransition x0 => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.LaneTransition (toPoolV1PairLatePublicStatementErrorV1 (x0))
  | .Afterstate x0 => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Afterstate (toPoolV1PairVerifierTransportErrorV1 (x0))
  | .Account x0 => AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Account (toPoolV1PairForestAccountErrorV1 (x0))

def fromPoolV1PairForestTerminalFormatErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 :=
  match value with
  | .WrongLength => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength
  | .WrongMagic => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongMagic
  | .WrongVersion => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongVersion
  | .WrongDigestEncoding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding
  | .InvalidTransitionKind => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.InvalidTransitionKind
  | .InvalidOutputLane => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.InvalidOutputLane
  | .NonZeroBinding => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding
  | .NonCanonicalDigest => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonCanonicalDigest
  | .OutputLaneMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.OutputLaneMismatch
  | .MasterBindingMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.MasterBindingMismatch
  | .DeploymentBindingMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.DeploymentBindingMismatch
  | .HistoricalAnchorMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.HistoricalAnchorMismatch
  | .CheckpointBindingMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CheckpointBindingMismatch
  | .SelectedLaneBindingMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.SelectedLaneBindingMismatch
  | .LiveSnapshotMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.LiveSnapshotMismatch
  | .CandidateAfterstateMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.CandidateAfterstateMismatch
  | .ResultBindingMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.ResultBindingMismatch
  | .WithdrawalDestinationMismatch => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WithdrawalDestinationMismatch
  | .Payment x0 => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Payment (fromPoolV1PaymentStatementFormatError (x0))
  | .LaneTransition x0 => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.LaneTransition (fromPoolV1PairLatePublicStatementErrorV1 (x0))
  | .Afterstate x0 => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Afterstate (fromPoolV1PairVerifierTransportErrorV1 (x0))
  | .Account x0 => AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.Account (fromPoolV1PairForestAccountErrorV1 (x0))

@[simp] theorem from_toPoolV1PairForestTerminalFormatErrorV1 (value : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : fromPoolV1PairForestTerminalFormatErrorV1 (toPoolV1PairForestTerminalFormatErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairForestTerminalFormatErrorV1,fromPoolV1PairForestTerminalFormatErrorV1,from_toPoolV1TransitionKind,from_toPoolV1TreeError,from_toPoolV1PairForestAccountErrorV1,from_toPoolV1PairLiveSnapshotV1,from_toPoolV1PairVerifiedAfterstateV1,from_toPoolV1PairLatePublicStatementV1,from_toPoolV1PairForestTerminalCommonV1,from_toPoolV1WithdrawalPublicV1,from_toPoolV1PrivateTransferPublicV1,from_toPoolV1PairForestTerminalStatementV1,from_toPoolV1PaymentStatementFormatError,from_toPoolV1PairLiveSnapshotErrorV1,from_toPoolV1PairVerifierTransportErrorV1,from_toPoolV1PairLatePublicStatementErrorV1]
  all_goals rfl

@[simp] theorem to_fromPoolV1PairForestTerminalFormatErrorV1 (value : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : toPoolV1PairForestTerminalFormatErrorV1 (fromPoolV1PairForestTerminalFormatErrorV1 value)=value := by
  cases value <;> simp only [toPoolV1PairForestTerminalFormatErrorV1,fromPoolV1PairForestTerminalFormatErrorV1,to_fromPoolV1TransitionKind,to_fromPoolV1TreeError,to_fromPoolV1PairForestAccountErrorV1,to_fromPoolV1PairLiveSnapshotV1,to_fromPoolV1PairVerifiedAfterstateV1,to_fromPoolV1PairLatePublicStatementV1,to_fromPoolV1PairForestTerminalCommonV1,to_fromPoolV1WithdrawalPublicV1,to_fromPoolV1PrivateTransferPublicV1,to_fromPoolV1PairForestTerminalStatementV1,to_fromPoolV1PaymentStatementFormatError,to_fromPoolV1PairLiveSnapshotErrorV1,to_fromPoolV1PairVerifierTransportErrorV1,to_fromPoolV1PairLatePublicStatementErrorV1]
  all_goals rfl

def equivPoolV1PairForestTerminalFormatErrorV1 : AspisS6FullForestEncoderNamed.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 ≃ AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 where
  toFun := toPoolV1PairForestTerminalFormatErrorV1
  invFun := fromPoolV1PairForestTerminalFormatErrorV1
  left_inv := from_toPoolV1PairForestTerminalFormatErrorV1
  right_inv := to_fromPoolV1PairForestTerminalFormatErrorV1

#print axioms equivPoolV1PairForestTerminalFormatErrorV1

end AspisS6OuterCarrierBridge
