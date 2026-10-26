import RPz7_S2K_AfterstateEncoding
import S6AfterstateFrameBytesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeAfterstateEncoderReuse
namespace Native
abbrev Afterstate := AspisR1TerminalDecoder.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
end Native
abbrev ReferenceAfterstate := AspisS6FiveUnrolledCodec.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1

def native (a : ReferenceAfterstate) : Native.Afterstate :=
  {next_pair_index:=a.next_pair_index, next_root:=a.next_root, next_frontier:=a.next_frontier}

theorem accepted_encoder_bytes (a : Native.Afterstate) (encoded : Array U8 688#usize)
    (accepted : AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 a=
      ok (core.result.Result.Ok encoded)) :
    encoded=AspisR1.S2K.AfterstateEncoding.bytes a := by
  have validated := (AspisR1.S2K.AfterstateStatus.status_exact a).symm
  rw [accepted] at validated
  have hv : AspisR1TerminalDecoder.pool_v1.pair_terminal.validate_verified_afterstate a=
      ok (core.result.Result.Ok ()) := validated
  have exactBytes := AspisR1.S2K.AfterstateEncoding.encode_exact a hv
  rw [accepted] at exactBytes
  cases exactBytes
  rfl

#print axioms accepted_encoder_bytes
end AspisS6NativeAfterstateEncoderReuse
