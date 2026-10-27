import RPz7_S6NativeSnapshotDecodedFramesV1
import RPz7_S6NativeSnapshotDecodeTotalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecodeTotal
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeSnapshotDecoderFactored
open AspisS6NativeSnapshotDecoderFactored.Frames

/-- Sole premise: the actual native decoder accepted these bytes. -/
theorem accepted_frames (bytes : Slice U8) (snapshot : PoolV1PairLiveSnapshotV1)
    (accepted : decode_pool_v1_pair_live_snapshot_v1 bytes=ok (core.result.Result.Ok snapshot)) :
    full_frame bytes snapshot := by
  have frames := decode_frames bytes
  rw [decode_source bytes,accepted,WP.spec_ok] at frames
  exact frames snapshot rfl

#print axioms accepted_frames
end AspisS6NativeSnapshotDecodeTotal
