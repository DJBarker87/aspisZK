import S6SourceAfterstateDecodedFramesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.AfterstateFactored.Frames
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

/-- Complete accepted field provenance from the actual complete decoder.
The sole premise is its actual successful Rust return on the same input. -/
theorem source_accepted_frames (bytes : Slice U8)
    (afterstate : PoolV1PairVerifiedAfterstateV1)
    (accepted : decode_pool_v1_pair_verified_afterstate_v1 bytes=
      ok (core.result.Result.Ok afterstate)) : full_frame bytes afterstate := by
  have frames := decode_frames bytes
  rw [decode_source bytes, accepted, WP.spec_ok] at frames
  exact frames afterstate rfl

#print axioms source_accepted_frames
end AspisS6SourceCodec.AfterstateFactored.Frames
