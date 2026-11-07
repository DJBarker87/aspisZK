import NMT_345Dec_T12
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT13 : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .InvalidTransitionKind => .InvalidTransitionKind
 | .InvalidOutputLane => .InvalidOutputLane
 | .NonZeroBinding => .NonZeroBinding
 | .NonCanonicalDigest => .NonCanonicalDigest
 | .OutputLaneMismatch => .OutputLaneMismatch
 | .MasterBindingMismatch => .MasterBindingMismatch
 | .DeploymentBindingMismatch => .DeploymentBindingMismatch
 | .HistoricalAnchorMismatch => .HistoricalAnchorMismatch
 | .CheckpointBindingMismatch => .CheckpointBindingMismatch
 | .SelectedLaneBindingMismatch => .SelectedLaneBindingMismatch
 | .LiveSnapshotMismatch => .LiveSnapshotMismatch
 | .CandidateAfterstateMismatch => .CandidateAfterstateMismatch
 | .ResultBindingMismatch => .ResultBindingMismatch
 | .WithdrawalDestinationMismatch => .WithdrawalDestinationMismatch
 | .Payment x0 => .Payment (toT9 (x0))
 | .LaneTransition x0 => .LaneTransition (toT12 (x0))
 | .Afterstate x0 => .Afterstate (toT11 (x0))
 | .Account x0 => .Account (toT1 (x0))
def fromT13 : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1 → NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .InvalidTransitionKind => .InvalidTransitionKind
 | .InvalidOutputLane => .InvalidOutputLane
 | .NonZeroBinding => .NonZeroBinding
 | .NonCanonicalDigest => .NonCanonicalDigest
 | .OutputLaneMismatch => .OutputLaneMismatch
 | .MasterBindingMismatch => .MasterBindingMismatch
 | .DeploymentBindingMismatch => .DeploymentBindingMismatch
 | .HistoricalAnchorMismatch => .HistoricalAnchorMismatch
 | .CheckpointBindingMismatch => .CheckpointBindingMismatch
 | .SelectedLaneBindingMismatch => .SelectedLaneBindingMismatch
 | .LiveSnapshotMismatch => .LiveSnapshotMismatch
 | .CandidateAfterstateMismatch => .CandidateAfterstateMismatch
 | .ResultBindingMismatch => .ResultBindingMismatch
 | .WithdrawalDestinationMismatch => .WithdrawalDestinationMismatch
 | .Payment x0 => .Payment (fromT9 (x0))
 | .LaneTransition x0 => .LaneTransition (fromT12 (x0))
 | .Afterstate x0 => .Afterstate (fromT11 (x0))
 | .Account x0 => .Account (fromT1 (x0))
@[simp] theorem toT13_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : fromT13 (toT13 x) = x := by
 cases x <;> simp [toT13,fromT13]
#print axioms toT13_inverse
@[simp] theorem fromT13_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1) : toT13 (fromT13 x) = x := by
 cases x <;> simp [fromT13,toT13]
#print axioms fromT13_inverse
end NMT_345Dec
