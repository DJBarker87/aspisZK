import LaneEncoderActualDigestDecodeRoundtripV7
import LaneEncoderRootAndAllFrontierBytes
import AspisR1PairForestLaneEncoderTailSourceCut.Funs
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailActualRootAndFrontierDecode
open AspisR1PairForestLaneEncoderTailSourceCut Aeneas Aeneas.Std Result

def DigestCanonical (digest : Array M31 8#usize) : Prop :=
  ∀ i : Usize, i.val < 8 → ∀ value : M31,
    Array.index_usize digest i = .ok value → value.val < 2147483647

theorem successful_tail_root_and_frontier_actual_decode
    (lane : PoolV1PairForestLaneStateV1) (out : Array U8 768#usize)
    (hok : encode_lane_bytes_tail_v1 lane = .ok out)
    (hcanonical : ∀ digest : Array M31 8#usize, DigestCanonical digest) :
    ∃ rootBytes : Array U8 32#usize,
      encode_digest_canonical lane.tree.root = .ok rootBytes ∧
      (∀ k : Nat, k < 32 → out.val[96 + k]? = rootBytes.val[k]?) ∧
      AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical rootBytes = .ok (.Ok lane.tree.root) ∧
      (∃ row_0 : Array M31 8#usize, ∃ bytes_0 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 0#usize = .ok row_0 ∧
        encode_digest_canonical row_0 = .ok bytes_0 ∧
        (∀ k : Nat, k < 32 → out.val[128 + k]? = bytes_0.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_0 = .ok (.Ok row_0)) ∧
      (∃ row_1 : Array M31 8#usize, ∃ bytes_1 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 1#usize = .ok row_1 ∧
        encode_digest_canonical row_1 = .ok bytes_1 ∧
        (∀ k : Nat, k < 32 → out.val[160 + k]? = bytes_1.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_1 = .ok (.Ok row_1)) ∧
      (∃ row_2 : Array M31 8#usize, ∃ bytes_2 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 2#usize = .ok row_2 ∧
        encode_digest_canonical row_2 = .ok bytes_2 ∧
        (∀ k : Nat, k < 32 → out.val[192 + k]? = bytes_2.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_2 = .ok (.Ok row_2)) ∧
      (∃ row_3 : Array M31 8#usize, ∃ bytes_3 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 3#usize = .ok row_3 ∧
        encode_digest_canonical row_3 = .ok bytes_3 ∧
        (∀ k : Nat, k < 32 → out.val[224 + k]? = bytes_3.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_3 = .ok (.Ok row_3)) ∧
      (∃ row_4 : Array M31 8#usize, ∃ bytes_4 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 4#usize = .ok row_4 ∧
        encode_digest_canonical row_4 = .ok bytes_4 ∧
        (∀ k : Nat, k < 32 → out.val[256 + k]? = bytes_4.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_4 = .ok (.Ok row_4)) ∧
      (∃ row_5 : Array M31 8#usize, ∃ bytes_5 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 5#usize = .ok row_5 ∧
        encode_digest_canonical row_5 = .ok bytes_5 ∧
        (∀ k : Nat, k < 32 → out.val[288 + k]? = bytes_5.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_5 = .ok (.Ok row_5)) ∧
      (∃ row_6 : Array M31 8#usize, ∃ bytes_6 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 6#usize = .ok row_6 ∧
        encode_digest_canonical row_6 = .ok bytes_6 ∧
        (∀ k : Nat, k < 32 → out.val[320 + k]? = bytes_6.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_6 = .ok (.Ok row_6)) ∧
      (∃ row_7 : Array M31 8#usize, ∃ bytes_7 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 7#usize = .ok row_7 ∧
        encode_digest_canonical row_7 = .ok bytes_7 ∧
        (∀ k : Nat, k < 32 → out.val[352 + k]? = bytes_7.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_7 = .ok (.Ok row_7)) ∧
      (∃ row_8 : Array M31 8#usize, ∃ bytes_8 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 8#usize = .ok row_8 ∧
        encode_digest_canonical row_8 = .ok bytes_8 ∧
        (∀ k : Nat, k < 32 → out.val[384 + k]? = bytes_8.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_8 = .ok (.Ok row_8)) ∧
      (∃ row_9 : Array M31 8#usize, ∃ bytes_9 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 9#usize = .ok row_9 ∧
        encode_digest_canonical row_9 = .ok bytes_9 ∧
        (∀ k : Nat, k < 32 → out.val[416 + k]? = bytes_9.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_9 = .ok (.Ok row_9)) ∧
      (∃ row_10 : Array M31 8#usize, ∃ bytes_10 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 10#usize = .ok row_10 ∧
        encode_digest_canonical row_10 = .ok bytes_10 ∧
        (∀ k : Nat, k < 32 → out.val[448 + k]? = bytes_10.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_10 = .ok (.Ok row_10)) ∧
      (∃ row_11 : Array M31 8#usize, ∃ bytes_11 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 11#usize = .ok row_11 ∧
        encode_digest_canonical row_11 = .ok bytes_11 ∧
        (∀ k : Nat, k < 32 → out.val[480 + k]? = bytes_11.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_11 = .ok (.Ok row_11)) ∧
      (∃ row_12 : Array M31 8#usize, ∃ bytes_12 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 12#usize = .ok row_12 ∧
        encode_digest_canonical row_12 = .ok bytes_12 ∧
        (∀ k : Nat, k < 32 → out.val[512 + k]? = bytes_12.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_12 = .ok (.Ok row_12)) ∧
      (∃ row_13 : Array M31 8#usize, ∃ bytes_13 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 13#usize = .ok row_13 ∧
        encode_digest_canonical row_13 = .ok bytes_13 ∧
        (∀ k : Nat, k < 32 → out.val[544 + k]? = bytes_13.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_13 = .ok (.Ok row_13)) ∧
      (∃ row_14 : Array M31 8#usize, ∃ bytes_14 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 14#usize = .ok row_14 ∧
        encode_digest_canonical row_14 = .ok bytes_14 ∧
        (∀ k : Nat, k < 32 → out.val[576 + k]? = bytes_14.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_14 = .ok (.Ok row_14)) ∧
      (∃ row_15 : Array M31 8#usize, ∃ bytes_15 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 15#usize = .ok row_15 ∧
        encode_digest_canonical row_15 = .ok bytes_15 ∧
        (∀ k : Nat, k < 32 → out.val[608 + k]? = bytes_15.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_15 = .ok (.Ok row_15)) ∧
      (∃ row_16 : Array M31 8#usize, ∃ bytes_16 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 16#usize = .ok row_16 ∧
        encode_digest_canonical row_16 = .ok bytes_16 ∧
        (∀ k : Nat, k < 32 → out.val[640 + k]? = bytes_16.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_16 = .ok (.Ok row_16)) ∧
      (∃ row_17 : Array M31 8#usize, ∃ bytes_17 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 17#usize = .ok row_17 ∧
        encode_digest_canonical row_17 = .ok bytes_17 ∧
        (∀ k : Nat, k < 32 → out.val[672 + k]? = bytes_17.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_17 = .ok (.Ok row_17)) ∧
      (∃ row_18 : Array M31 8#usize, ∃ bytes_18 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 18#usize = .ok row_18 ∧
        encode_digest_canonical row_18 = .ok bytes_18 ∧
        (∀ k : Nat, k < 32 → out.val[704 + k]? = bytes_18.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_18 = .ok (.Ok row_18)) ∧
      (∃ row_19 : Array M31 8#usize, ∃ bytes_19 : Array U8 32#usize,
        Array.index_usize lane.tree.frontier 19#usize = .ok row_19 ∧
        encode_digest_canonical row_19 = .ok bytes_19 ∧
        (∀ k : Nat, k < 32 → out.val[736 + k]? = bytes_19.val[k]?) ∧
        AspisR1TerminalDecoder.atomic_statement.decode_digest_canonical bytes_19 = .ok (.Ok row_19)) := by
  obtain ⟨rootBytes, hrootEnc, hrootBytes, hrows⟩ :=
    AspisR1PairForestLaneEncoderTailActualRootBlock.successful_tail_root_and_all_frontier_bytes lane out hok
  have hrootDecode := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    lane.tree.root rootBytes hrootEnc (hcanonical lane.tree.root)
  have hrow_0 := hrows.1
  have htail_0 := hrows.2
  rcases hrow_0 with ⟨row_0, bytes_0, hindex_0, hencode_0, hwindow_0⟩
  clear hrows
  have hrows := htail_0
  have hdecode_0 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_0 bytes_0 hencode_0 (hcanonical row_0)
  have hrow_1 := hrows.1
  have htail_1 := hrows.2
  rcases hrow_1 with ⟨row_1, bytes_1, hindex_1, hencode_1, hwindow_1⟩
  clear hrows
  have hrows := htail_1
  have hdecode_1 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_1 bytes_1 hencode_1 (hcanonical row_1)
  have hrow_2 := hrows.1
  have htail_2 := hrows.2
  rcases hrow_2 with ⟨row_2, bytes_2, hindex_2, hencode_2, hwindow_2⟩
  clear hrows
  have hrows := htail_2
  have hdecode_2 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_2 bytes_2 hencode_2 (hcanonical row_2)
  have hrow_3 := hrows.1
  have htail_3 := hrows.2
  rcases hrow_3 with ⟨row_3, bytes_3, hindex_3, hencode_3, hwindow_3⟩
  clear hrows
  have hrows := htail_3
  have hdecode_3 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_3 bytes_3 hencode_3 (hcanonical row_3)
  have hrow_4 := hrows.1
  have htail_4 := hrows.2
  rcases hrow_4 with ⟨row_4, bytes_4, hindex_4, hencode_4, hwindow_4⟩
  clear hrows
  have hrows := htail_4
  have hdecode_4 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_4 bytes_4 hencode_4 (hcanonical row_4)
  have hrow_5 := hrows.1
  have htail_5 := hrows.2
  rcases hrow_5 with ⟨row_5, bytes_5, hindex_5, hencode_5, hwindow_5⟩
  clear hrows
  have hrows := htail_5
  have hdecode_5 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_5 bytes_5 hencode_5 (hcanonical row_5)
  have hrow_6 := hrows.1
  have htail_6 := hrows.2
  rcases hrow_6 with ⟨row_6, bytes_6, hindex_6, hencode_6, hwindow_6⟩
  clear hrows
  have hrows := htail_6
  have hdecode_6 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_6 bytes_6 hencode_6 (hcanonical row_6)
  have hrow_7 := hrows.1
  have htail_7 := hrows.2
  rcases hrow_7 with ⟨row_7, bytes_7, hindex_7, hencode_7, hwindow_7⟩
  clear hrows
  have hrows := htail_7
  have hdecode_7 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_7 bytes_7 hencode_7 (hcanonical row_7)
  have hrow_8 := hrows.1
  have htail_8 := hrows.2
  rcases hrow_8 with ⟨row_8, bytes_8, hindex_8, hencode_8, hwindow_8⟩
  clear hrows
  have hrows := htail_8
  have hdecode_8 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_8 bytes_8 hencode_8 (hcanonical row_8)
  have hrow_9 := hrows.1
  have htail_9 := hrows.2
  rcases hrow_9 with ⟨row_9, bytes_9, hindex_9, hencode_9, hwindow_9⟩
  clear hrows
  have hrows := htail_9
  have hdecode_9 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_9 bytes_9 hencode_9 (hcanonical row_9)
  have hrow_10 := hrows.1
  have htail_10 := hrows.2
  rcases hrow_10 with ⟨row_10, bytes_10, hindex_10, hencode_10, hwindow_10⟩
  clear hrows
  have hrows := htail_10
  have hdecode_10 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_10 bytes_10 hencode_10 (hcanonical row_10)
  have hrow_11 := hrows.1
  have htail_11 := hrows.2
  rcases hrow_11 with ⟨row_11, bytes_11, hindex_11, hencode_11, hwindow_11⟩
  clear hrows
  have hrows := htail_11
  have hdecode_11 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_11 bytes_11 hencode_11 (hcanonical row_11)
  have hrow_12 := hrows.1
  have htail_12 := hrows.2
  rcases hrow_12 with ⟨row_12, bytes_12, hindex_12, hencode_12, hwindow_12⟩
  clear hrows
  have hrows := htail_12
  have hdecode_12 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_12 bytes_12 hencode_12 (hcanonical row_12)
  have hrow_13 := hrows.1
  have htail_13 := hrows.2
  rcases hrow_13 with ⟨row_13, bytes_13, hindex_13, hencode_13, hwindow_13⟩
  clear hrows
  have hrows := htail_13
  have hdecode_13 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_13 bytes_13 hencode_13 (hcanonical row_13)
  have hrow_14 := hrows.1
  have htail_14 := hrows.2
  rcases hrow_14 with ⟨row_14, bytes_14, hindex_14, hencode_14, hwindow_14⟩
  clear hrows
  have hrows := htail_14
  have hdecode_14 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_14 bytes_14 hencode_14 (hcanonical row_14)
  have hrow_15 := hrows.1
  have htail_15 := hrows.2
  rcases hrow_15 with ⟨row_15, bytes_15, hindex_15, hencode_15, hwindow_15⟩
  clear hrows
  have hrows := htail_15
  have hdecode_15 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_15 bytes_15 hencode_15 (hcanonical row_15)
  have hrow_16 := hrows.1
  have htail_16 := hrows.2
  rcases hrow_16 with ⟨row_16, bytes_16, hindex_16, hencode_16, hwindow_16⟩
  clear hrows
  have hrows := htail_16
  have hdecode_16 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_16 bytes_16 hencode_16 (hcanonical row_16)
  have hrow_17 := hrows.1
  have htail_17 := hrows.2
  rcases hrow_17 with ⟨row_17, bytes_17, hindex_17, hencode_17, hwindow_17⟩
  clear hrows
  have hrows := htail_17
  have hdecode_17 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_17 bytes_17 hencode_17 (hcanonical row_17)
  have hrow_18 := hrows.1
  have htail_18 := hrows.2
  rcases hrow_18 with ⟨row_18, bytes_18, hindex_18, hencode_18, hwindow_18⟩
  clear hrows
  have hrows := htail_18
  have hdecode_18 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_18 bytes_18 hencode_18 (hcanonical row_18)
  rcases hrows with ⟨row_19, bytes_19, hindex_19, hencode_19, hwindow_19⟩
  have hdecode_19 := AspisR1PairForestLaneEncoderTailActualDigestDecodeRoundtrip.actual_decode_digest_after_successful_encode
    row_19 bytes_19 hencode_19 (hcanonical row_19)
  refine ⟨rootBytes, hrootEnc, And.intro hrootBytes (And.intro hrootDecode ?_)⟩
  refine And.intro (by exact ⟨row_0, bytes_0, hindex_0, hencode_0, hwindow_0, hdecode_0⟩) ?_
  refine And.intro (by exact ⟨row_1, bytes_1, hindex_1, hencode_1, hwindow_1, hdecode_1⟩) ?_
  refine And.intro (by exact ⟨row_2, bytes_2, hindex_2, hencode_2, hwindow_2, hdecode_2⟩) ?_
  refine And.intro (by exact ⟨row_3, bytes_3, hindex_3, hencode_3, hwindow_3, hdecode_3⟩) ?_
  refine And.intro (by exact ⟨row_4, bytes_4, hindex_4, hencode_4, hwindow_4, hdecode_4⟩) ?_
  refine And.intro (by exact ⟨row_5, bytes_5, hindex_5, hencode_5, hwindow_5, hdecode_5⟩) ?_
  refine And.intro (by exact ⟨row_6, bytes_6, hindex_6, hencode_6, hwindow_6, hdecode_6⟩) ?_
  refine And.intro (by exact ⟨row_7, bytes_7, hindex_7, hencode_7, hwindow_7, hdecode_7⟩) ?_
  refine And.intro (by exact ⟨row_8, bytes_8, hindex_8, hencode_8, hwindow_8, hdecode_8⟩) ?_
  refine And.intro (by exact ⟨row_9, bytes_9, hindex_9, hencode_9, hwindow_9, hdecode_9⟩) ?_
  refine And.intro (by exact ⟨row_10, bytes_10, hindex_10, hencode_10, hwindow_10, hdecode_10⟩) ?_
  refine And.intro (by exact ⟨row_11, bytes_11, hindex_11, hencode_11, hwindow_11, hdecode_11⟩) ?_
  refine And.intro (by exact ⟨row_12, bytes_12, hindex_12, hencode_12, hwindow_12, hdecode_12⟩) ?_
  refine And.intro (by exact ⟨row_13, bytes_13, hindex_13, hencode_13, hwindow_13, hdecode_13⟩) ?_
  refine And.intro (by exact ⟨row_14, bytes_14, hindex_14, hencode_14, hwindow_14, hdecode_14⟩) ?_
  refine And.intro (by exact ⟨row_15, bytes_15, hindex_15, hencode_15, hwindow_15, hdecode_15⟩) ?_
  refine And.intro (by exact ⟨row_16, bytes_16, hindex_16, hencode_16, hwindow_16, hdecode_16⟩) ?_
  refine And.intro (by exact ⟨row_17, bytes_17, hindex_17, hencode_17, hwindow_17, hdecode_17⟩) ?_
  refine And.intro (by exact ⟨row_18, bytes_18, hindex_18, hencode_18, hwindow_18, hdecode_18⟩) ?_
  exact ⟨row_19, bytes_19, hindex_19, hencode_19, hwindow_19, hdecode_19⟩

#print axioms successful_tail_root_and_frontier_actual_decode
end AspisR1PairForestLaneEncoderTailActualRootAndFrontierDecode
