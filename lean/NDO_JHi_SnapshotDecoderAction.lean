import NDO_JHi_SnapshotConstants
set_option autoImplicit false
namespace AspisR1.JHi_SnapshotDecoderAction
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct JHi_SnapshotBody

theorem source (value : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) (output : Slice U8)
    (size : Slice.len output=800#usize)
    (validated : AspisR1TerminalDecoder.pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 value=ok (.Ok ())) :
    AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 value output=
    (body value output >>= fun out=>ok (core.result.Result.Ok (),out)) := by
  unfold AspisR1TerminalDecoder.pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1
  rw [size]
  simp only [AspisR1TerminalDecoder.pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES,show (800#usize !=800#usize)=false from rfl,Bool.false_eq_true,↓reduceIte]
  rw [validated]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [body,bind_assoc_eq,bind_tc_ok,Aeneas.Std.uncurry,
    JHi_DigestAssociation.encode,JHi_SnapshotLoopAssociation.source,JHi_SnapshotConstants.c0,JHi_SnapshotConstants.c1,JHi_SnapshotConstants.c2,JHi_SnapshotConstants.c3,JHi_SnapshotConstants.c4,JHi_SnapshotConstants.c5,JHi_SnapshotConstants.c6]
  congr 1
#print axioms source
end AspisR1.JHi_SnapshotDecoderAction
