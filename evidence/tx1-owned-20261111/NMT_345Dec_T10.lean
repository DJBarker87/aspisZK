import NMT_345Dec_T9
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT10 : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongFormatBinding => .WrongFormatBinding
 | .NonZeroReserved => .NonZeroReserved
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .SequenceIndexMismatch => .SequenceIndexMismatch
 | .TreeFull => .TreeFull
 | .NonCanonicalDigest => .NonCanonicalDigest
def fromT10 : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 → NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongFormatBinding => .WrongFormatBinding
 | .NonZeroReserved => .NonZeroReserved
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .SequenceIndexMismatch => .SequenceIndexMismatch
 | .TreeFull => .TreeFull
 | .NonCanonicalDigest => .NonCanonicalDigest
@[simp] theorem toT10_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : fromT10 (toT10 x) = x := by
 cases x <;> simp [toT10,fromT10]
#print axioms toT10_inverse
@[simp] theorem fromT10_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1) : toT10 (fromT10 x) = x := by
 cases x <;> simp [fromT10,toT10]
#print axioms fromT10_inverse
end NMT_345Dec
