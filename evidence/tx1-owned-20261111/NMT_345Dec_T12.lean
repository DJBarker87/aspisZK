import NMT_345Dec_T11
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT12 : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongItemCount => .WrongItemCount
 | .WrongHeaderLength => .WrongHeaderLength
 | .WrongSnapshotLength => .WrongSnapshotLength
 | .WrongAfterstateLength => .WrongAfterstateLength
 | .WrongTotalLength => .WrongTotalLength
 | .NonZeroReserved => .NonZeroReserved
 | .Snapshot x0 => .Snapshot (toT10 (x0))
 | .Afterstate x0 => .Afterstate (toT11 (x0))
 | .AfterstateIndexMismatch => .AfterstateIndexMismatch
def fromT12 : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1 → NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongItemCount => .WrongItemCount
 | .WrongHeaderLength => .WrongHeaderLength
 | .WrongSnapshotLength => .WrongSnapshotLength
 | .WrongAfterstateLength => .WrongAfterstateLength
 | .WrongTotalLength => .WrongTotalLength
 | .NonZeroReserved => .NonZeroReserved
 | .Snapshot x0 => .Snapshot (fromT10 (x0))
 | .Afterstate x0 => .Afterstate (fromT11 (x0))
 | .AfterstateIndexMismatch => .AfterstateIndexMismatch
@[simp] theorem toT12_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : fromT12 (toT12 x) = x := by
 cases x <;> simp [toT12,fromT12]
#print axioms toT12_inverse
@[simp] theorem fromT12_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) : toT12 (fromT12 x) = x := by
 cases x <;> simp [fromT12,toT12]
#print axioms fromT12_inverse
end NMT_345Dec
