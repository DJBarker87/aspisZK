import LaneEncoderCursorBytes
import LaneEncoderCursorCodecRoundtripV23
import Aeneas.Std

set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailCursorValue
open Aeneas Aeneas.Std Result

theorem successful_tail_cursor_value
    (lane : AspisR1PairForestLaneEncoderTailSourceCut.PoolV1PairForestLaneStateV1)
    (out : Array U8 768#usize)
    (hok : AspisR1PairForestLaneEncoderTailSourceCut.encode_lane_bytes_tail_v1 lane = .ok out) :
    ∃ cursorBytes : Array U8 8#usize,
      lift (core.num.U64.to_le_bytes lane.tree.next_leaf_index) = .ok cursorBytes ∧
      (∀ k : Nat, k < 8 → out.val[88 + k]? = cursorBytes.val[k]?) ∧
      core.num.U64.from_le_bytes cursorBytes = lane.tree.next_leaf_index := by
  obtain ⟨cursorBytes, hencode, hprojection⟩ :=
    AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_cursor_bytes
      lane out hok
  refine ⟨cursorBytes, hencode, hprojection, ?_⟩
  have hbytes : core.num.U64.to_le_bytes lane.tree.next_leaf_index = cursorBytes := by
    simpa [lift] using hencode
  rw [← hbytes]
  exact AspisR1PairForestLaneEncoderTailCursorCodec.u64_from_to_le lane.tree.next_leaf_index

#print axioms successful_tail_cursor_value
end AspisR1PairForestLaneEncoderTailCursorValue
