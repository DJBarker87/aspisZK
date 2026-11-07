import NMT_345Dec_T10
import NFY_Part058
set_option autoImplicit false
noncomputable section
namespace NMT_345Dec
open Aeneas Aeneas.Std AspisR1.NMT_Transport
def toT11 : NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 → AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongStatementVersion => .WrongStatementVersion
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .InvalidTransitionKind => .InvalidTransitionKind
 | .WrongSuccessCode => .WrongSuccessCode
 | .WrongPairFormat => .WrongPairFormat
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .InvalidProofBodyLength => .InvalidProofBodyLength
 | .InvalidStatementPayloadLength => .InvalidStatementPayloadLength
 | .InvalidLiveSnapshotPayloadLength => .InvalidLiveSnapshotPayloadLength
 | .NonCanonicalOutputPair => .NonCanonicalOutputPair
 | .InvalidAfterstateIndex => .InvalidAfterstateIndex
 | .NonCanonicalAfterstate => .NonCanonicalAfterstate
def fromT11 : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 → NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
 | .WrongLength => .WrongLength
 | .WrongMagic => .WrongMagic
 | .WrongVersion => .WrongVersion
 | .WrongStatementVersion => .WrongStatementVersion
 | .WrongDigestEncoding => .WrongDigestEncoding
 | .InvalidTransitionKind => .InvalidTransitionKind
 | .WrongSuccessCode => .WrongSuccessCode
 | .WrongPairFormat => .WrongPairFormat
 | .ZeroRequiredBinding => .ZeroRequiredBinding
 | .InvalidProofBodyLength => .InvalidProofBodyLength
 | .InvalidStatementPayloadLength => .InvalidStatementPayloadLength
 | .InvalidLiveSnapshotPayloadLength => .InvalidLiveSnapshotPayloadLength
 | .NonCanonicalOutputPair => .NonCanonicalOutputPair
 | .InvalidAfterstateIndex => .InvalidAfterstateIndex
 | .NonCanonicalAfterstate => .NonCanonicalAfterstate
@[simp] theorem toT11_inverse (x : NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : fromT11 (toT11 x) = x := by
 cases x <;> simp [toT11,fromT11]
#print axioms toT11_inverse
@[simp] theorem fromT11_inverse (x : AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) : toT11 (fromT11 x) = x := by
 cases x <;> simp [fromT11,toT11]
#print axioms fromT11_inverse
end NMT_345Dec
