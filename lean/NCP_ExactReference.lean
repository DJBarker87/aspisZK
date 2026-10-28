import NCP_HelperExtracted.Funs
import NCP_CallerDomains
set_option autoImplicit false
noncomputable section
namespace NCP_ExactReference
open Aeneas Aeneas.Std Result

def error : NCP_HelperExtracted.pool_v1.pair_terminal.NCP_PoolV1PairVerifierTransportErrorV1 →
    AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
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

def transport {N : Usize} (r : core.result.Result (Array U8 N)
    NCP_HelperExtracted.pool_v1.pair_terminal.NCP_PoolV1PairVerifierTransportErrorV1) :
    core.result.Result (Array U8 N)
      AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1 :=
  match r with
  | .Ok a => .Ok a
  | .Err e => .Err (error e)

theorem source (N : Usize) (bytes : Slice U8) :
    (do let r ← NCP_HelperExtracted.NCP_refs.NCP_exact_ref N bytes
        ok (transport r)) = AspisR1TerminalDecoder.pool_v1.pair_terminal.exact N bytes := by
  unfold NCP_HelperExtracted.NCP_refs.NCP_exact_ref
    AspisR1TerminalDecoder.pool_v1.pair_terminal.exact
  generalize h : core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 bytes = r
  cases r with
  | ok r => cases r <;> rfl
  | fail e => rfl
  | div => rfl

#print axioms source
end NCP_ExactReference
