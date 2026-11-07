import NMT_345Dec_T0
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT1 : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongLaneCount => .WrongLaneCount
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .WrongDepth => .WrongDepth
 | .WrongFormatBinding => .WrongFormatBinding
 | .NonZeroReserved => .NonZeroReserved
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .InvalidBoolean => .InvalidBoolean
 | .InvalidMasterState => .InvalidMasterState
 | .InvalidLane => .InvalidLane
 | .LaneMasterMismatch => .LaneMasterMismatch
 | .LaneOrderMismatch => .LaneOrderMismatch
 | .LaneSequenceDecreased => .LaneSequenceDecreased
 | .DuplicateCheckpoint => .DuplicateCheckpoint
 | .CheckpointSequenceOverflow => .CheckpointSequenceOverflow
 | .NonCanonicalDigest => .NonCanonicalDigest
 | .Identity => .Identity
 | .Policy => .Policy
 | .Tree x0 => .Tree (toT0 (x0))
def fromT1 : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1 → NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongLaneCount => .WrongLaneCount
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .WrongDepth => .WrongDepth
 | .WrongFormatBinding => .WrongFormatBinding
 | .NonZeroReserved => .NonZeroReserved
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .InvalidBoolean => .InvalidBoolean
 | .InvalidMasterState => .InvalidMasterState
 | .InvalidLane => .InvalidLane
 | .LaneMasterMismatch => .LaneMasterMismatch
 | .LaneOrderMismatch => .LaneOrderMismatch
 | .LaneSequenceDecreased => .LaneSequenceDecreased
 | .DuplicateCheckpoint => .DuplicateCheckpoint
 | .CheckpointSequenceOverflow => .CheckpointSequenceOverflow
 | .NonCanonicalDigest => .NonCanonicalDigest
 | .Identity => .Identity
 | .Policy => .Policy
 | .Tree x0 => .Tree (fromT0 (x0))
@[simp] theorem toT1_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : fromT1 (toT1 x) = x := by
 cases x <;> simp [toT1,fromT1]
#print axioms toT1_inverse
@[simp] theorem fromT1_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.PoolV1PairForestAccountErrorV1) : toT1 (fromT1 x) = x := by
 cases x <;> simp [fromT1,toT1]
#print axioms fromT1_inverse
end NMT_345Dec
