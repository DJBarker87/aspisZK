import R1Z.PV_RunJoin_CodecPrefixDomain29
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CodecError29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder.pool_v1.pair_tree_profile

def Path (bytes : Slice U8) (error : PoolV1PairLiveSnapshotErrorV1) : Prop := R1Z.PV_RunJoin_CodecPrefixDomain29.ErrorPath bytes error

theorem iff_path (bytes : Slice U8) (error : PoolV1PairLiveSnapshotErrorV1) :
    decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Err error) ↔ Path bytes error := by
  rw [← R1Z.PV_RunJoin_DecoderPrefix29.source]
  exact R1Z.PV_RunJoin_CodecPrefixDomain29.error_iff bytes error
#print axioms iff_path
end R1Z.PV_RunJoin_CodecError29
