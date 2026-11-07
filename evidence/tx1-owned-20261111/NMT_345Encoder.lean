import NMT_345Dec_T13
import NMT_345MapLaws
import NGE_NEM_EncoderFrame
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
abbrev Afterstate := NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
abbrev EncodeError := NMT_stage1_owned.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
/-- Concrete CLOSED278 interpretation; the entire [u8;688] Result is kept. -/
def encodeCall (a : Afterstate) : Result (core.result.Result (Array U8 688#usize) EncodeError) :=
 mapOuter (mapCore id NMT_345Dec.fromT11)
  (AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1
    (NMT_345Dec.toT5 a))
theorem encode_closed (a : Afterstate) : encodeCall a =
 mapOuter (mapCore id NMT_345Dec.fromT11)
  (NFY_NBN_EncoderSummary.after AspisR1TerminalDecoder.atomic_statement.encode_digest_canonical
    (NMT_345Dec.toT5 a)) := by
 have h := congrArg (fun x => x.1) (NGE_NEM_EncoderFrame.after_value_and_frame (NMT_345Dec.toT5 a) ())
 dsimp only at h
 unfold encodeCall
 rw [h]
#print axioms encode_closed
end NMT_345
