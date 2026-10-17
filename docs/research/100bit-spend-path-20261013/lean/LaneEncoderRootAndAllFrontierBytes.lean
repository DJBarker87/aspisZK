import LaneEncoderActualRootBytesV1
import LaneEncoderFrontier0Narrow
import LaneEncoderFrontier1Narrow
import LaneEncoderFrontier2Narrow
import LaneEncoderFrontier3Narrow
import LaneEncoderFrontier4Narrow
import LaneEncoderFrontier5Narrow
import LaneEncoderFrontier6Narrow
import LaneEncoderFrontier7Narrow
import LaneEncoderFrontier8Narrow
import LaneEncoderFrontier9Narrow
import LaneEncoderFrontier10Narrow
import LaneEncoderFrontier11Narrow
import LaneEncoderFrontier12Narrow
import LaneEncoderFrontier13Narrow
import LaneEncoderFrontier14Narrow
import LaneEncoderFrontier15Narrow
import LaneEncoderFrontier16Narrow
import LaneEncoderFrontier17Narrow
import LaneEncoderFrontier18Narrow
import LaneEncoderFrontier19Narrow

set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailActualRootBlock
open AspisR1PairForestLaneEncoderTailSourceCut Aeneas Aeneas.Std Result

theorem successful_tail_root_and_all_frontier_bytes
    (lane : PoolV1PairForestLaneStateV1) (out : Array U8 768#usize)
    (hok : encode_lane_bytes_tail_v1 lane = .ok out) :
    ∃ rootBytes : Array U8 32#usize,
      encode_digest_canonical lane.tree.root = .ok rootBytes ∧
      (∀ k : Nat, k < 32 → out.val[96 + k]? = rootBytes.val[k]?) ∧
      (∃ row_0 : Array M31 8#usize, ∃ bytes_0 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 0#usize = .ok row_0 ∧
        encode_digest_canonical row_0 = .ok bytes_0 ∧
        ∀ k : Nat, k < 32 → out.val[128 + k]? = bytes_0.val[k]?) ∧
      (∃ row_1 : Array M31 8#usize, ∃ bytes_1 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 1#usize = .ok row_1 ∧
        encode_digest_canonical row_1 = .ok bytes_1 ∧
        ∀ k : Nat, k < 32 → out.val[160 + k]? = bytes_1.val[k]?) ∧
      (∃ row_2 : Array M31 8#usize, ∃ bytes_2 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 2#usize = .ok row_2 ∧
        encode_digest_canonical row_2 = .ok bytes_2 ∧
        ∀ k : Nat, k < 32 → out.val[192 + k]? = bytes_2.val[k]?) ∧
      (∃ row_3 : Array M31 8#usize, ∃ bytes_3 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 3#usize = .ok row_3 ∧
        encode_digest_canonical row_3 = .ok bytes_3 ∧
        ∀ k : Nat, k < 32 → out.val[224 + k]? = bytes_3.val[k]?) ∧
      (∃ row_4 : Array M31 8#usize, ∃ bytes_4 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 4#usize = .ok row_4 ∧
        encode_digest_canonical row_4 = .ok bytes_4 ∧
        ∀ k : Nat, k < 32 → out.val[256 + k]? = bytes_4.val[k]?) ∧
      (∃ row_5 : Array M31 8#usize, ∃ bytes_5 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 5#usize = .ok row_5 ∧
        encode_digest_canonical row_5 = .ok bytes_5 ∧
        ∀ k : Nat, k < 32 → out.val[288 + k]? = bytes_5.val[k]?) ∧
      (∃ row_6 : Array M31 8#usize, ∃ bytes_6 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 6#usize = .ok row_6 ∧
        encode_digest_canonical row_6 = .ok bytes_6 ∧
        ∀ k : Nat, k < 32 → out.val[320 + k]? = bytes_6.val[k]?) ∧
      (∃ row_7 : Array M31 8#usize, ∃ bytes_7 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 7#usize = .ok row_7 ∧
        encode_digest_canonical row_7 = .ok bytes_7 ∧
        ∀ k : Nat, k < 32 → out.val[352 + k]? = bytes_7.val[k]?) ∧
      (∃ row_8 : Array M31 8#usize, ∃ bytes_8 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 8#usize = .ok row_8 ∧
        encode_digest_canonical row_8 = .ok bytes_8 ∧
        ∀ k : Nat, k < 32 → out.val[384 + k]? = bytes_8.val[k]?) ∧
      (∃ row_9 : Array M31 8#usize, ∃ bytes_9 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 9#usize = .ok row_9 ∧
        encode_digest_canonical row_9 = .ok bytes_9 ∧
        ∀ k : Nat, k < 32 → out.val[416 + k]? = bytes_9.val[k]?) ∧
      (∃ row_10 : Array M31 8#usize, ∃ bytes_10 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 10#usize = .ok row_10 ∧
        encode_digest_canonical row_10 = .ok bytes_10 ∧
        ∀ k : Nat, k < 32 → out.val[448 + k]? = bytes_10.val[k]?) ∧
      (∃ row_11 : Array M31 8#usize, ∃ bytes_11 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 11#usize = .ok row_11 ∧
        encode_digest_canonical row_11 = .ok bytes_11 ∧
        ∀ k : Nat, k < 32 → out.val[480 + k]? = bytes_11.val[k]?) ∧
      (∃ row_12 : Array M31 8#usize, ∃ bytes_12 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 12#usize = .ok row_12 ∧
        encode_digest_canonical row_12 = .ok bytes_12 ∧
        ∀ k : Nat, k < 32 → out.val[512 + k]? = bytes_12.val[k]?) ∧
      (∃ row_13 : Array M31 8#usize, ∃ bytes_13 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 13#usize = .ok row_13 ∧
        encode_digest_canonical row_13 = .ok bytes_13 ∧
        ∀ k : Nat, k < 32 → out.val[544 + k]? = bytes_13.val[k]?) ∧
      (∃ row_14 : Array M31 8#usize, ∃ bytes_14 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 14#usize = .ok row_14 ∧
        encode_digest_canonical row_14 = .ok bytes_14 ∧
        ∀ k : Nat, k < 32 → out.val[576 + k]? = bytes_14.val[k]?) ∧
      (∃ row_15 : Array M31 8#usize, ∃ bytes_15 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 15#usize = .ok row_15 ∧
        encode_digest_canonical row_15 = .ok bytes_15 ∧
        ∀ k : Nat, k < 32 → out.val[608 + k]? = bytes_15.val[k]?) ∧
      (∃ row_16 : Array M31 8#usize, ∃ bytes_16 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 16#usize = .ok row_16 ∧
        encode_digest_canonical row_16 = .ok bytes_16 ∧
        ∀ k : Nat, k < 32 → out.val[640 + k]? = bytes_16.val[k]?) ∧
      (∃ row_17 : Array M31 8#usize, ∃ bytes_17 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 17#usize = .ok row_17 ∧
        encode_digest_canonical row_17 = .ok bytes_17 ∧
        ∀ k : Nat, k < 32 → out.val[672 + k]? = bytes_17.val[k]?) ∧
      (∃ row_18 : Array M31 8#usize, ∃ bytes_18 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 18#usize = .ok row_18 ∧
        encode_digest_canonical row_18 = .ok bytes_18 ∧
        ∀ k : Nat, k < 32 → out.val[704 + k]? = bytes_18.val[k]?) ∧
      (∃ row_19 : Array M31 8#usize, ∃ bytes_19 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 19#usize = .ok row_19 ∧
        encode_digest_canonical row_19 = .ok bytes_19 ∧
        ∀ k : Nat, k < 32 → out.val[736 + k]? = bytes_19.val[k]?) := by
  obtain ⟨rootBytes, hroot, hrootBytes⟩ := successful_tail_preserves_root_bytes lane out hok
  refine ⟨rootBytes, hroot, hrootBytes, ?_⟩
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_0_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_1_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_2_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_3_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_4_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_5_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_6_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_7_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_8_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_9_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_10_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_11_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_12_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_13_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_14_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_15_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_16_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_17_bytes lane out hok
  constructor
  · exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_18_bytes lane out hok
  exact AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_preserves_frontier_19_bytes lane out hok

#print axioms successful_tail_root_and_all_frontier_bytes
end AspisR1PairForestLaneEncoderTailActualRootBlock
