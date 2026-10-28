import R1Z.PV_RunJoin_CodecPrefixContinuation30
import R1Z.PV_RunJoin_CodecSuccess29
import R1Z.PV_RunJoin_CodecError29
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CodecComposition30
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder.pool_v1.pair_tree_profile
open PV_RunJoin_ResultDomain28 PV_RunJoin_CodecContinuationBase30

def Path (bytes : Slice U8) (post : PoolV1PairLiveSnapshotV1 → Prop) : Prop :=
  PV_RunJoin_CodecPrefixContinuation30.Path bytes post

theorem source_iff (bytes : Slice U8) (post : PoolV1PairLiveSnapshotV1 → Prop) :
    (∃ s, decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Ok s) ∧ post s) ↔
      Path bytes post := by
  rw [← wp_accepts,← PV_RunJoin_DecoderPrefix29.source]
  exact PV_RunJoin_CodecPrefixContinuation30.path_wp bytes post
#print axioms source_iff

theorem accepted_codec_domain (bytes : Slice U8) :
    Path bytes (fun _ => True) ↔ PV_RunJoin_CodecSuccess29.Path bytes := by
  rw [← source_iff]
  simp only [and_true]
  exact PV_RunJoin_CodecSuccess29.iff_path bytes
#print axioms accepted_codec_domain

theorem rejection (bytes : Slice U8) (error : PoolV1PairLiveSnapshotErrorV1)
    (h : PV_RunJoin_CodecError29.Path bytes error) :
    decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Err error) :=
  (PV_RunJoin_CodecError29.iff_path bytes error).mpr h
#print axioms rejection
end R1Z.PV_RunJoin_CodecComposition30
