import AspisR1PairForestLaneEncoderTailSourceCut.Funs
import AspisR1PairForestLaneEncoderTailRootProjectionExact
import AspisR1PairForestLaneEncoderTailRangeWriteFrameV5
import Aeneas.Std

set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailActualRootBlock
open Aeneas Aeneas.Std Result AspisR1PairForestLaneEncoderTailSourceCut

theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β} {x : β}
    (h : Bind.bind r f = .ok x) : ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h
theorem successful_tail_preserves_frontier_5_bytes (lane : PoolV1PairForestLaneStateV1) (out : Array U8 768#usize)
    (hok : encode_lane_bytes_tail_v1 lane = .ok out) :
    ∃ row : Array M31 8#usize, ∃ bytes : Array U8 32#usize,
      Array.index_usize lane.tree.frontier 5#usize = .ok row ∧
      encode_digest_canonical row = .ok bytes ∧
      ∀ k : Nat, k < 32 → out.val[288 + k]? = bytes.val[k]? := by
  have h := hok
  unfold encode_lane_bytes_tail_v1 at h
  rcases bind_ok_inv h with ⟨v1, hstep1, hrest1⟩
  rcases v1 with ⟨x1, y1⟩
  rcases bind_ok_inv hrest1 with ⟨v2, hstep2, hrest2⟩
  rcases bind_ok_inv hrest2 with ⟨v3, hstep3, hrest3⟩
  rcases bind_ok_inv hrest3 with ⟨v4, hstep4, hrest4⟩
  rcases bind_ok_inv hrest4 with ⟨v5, hstep5, hrest5⟩
  rcases bind_ok_inv hrest5 with ⟨v6, hstep6, hrest6⟩
  rcases bind_ok_inv hrest6 with ⟨v7, hstep7, hrest7⟩
  rcases bind_ok_inv hrest7 with ⟨v8, hstep8, hrest8⟩
  rcases bind_ok_inv hrest8 with ⟨v9, hstep9, hrest9⟩
  rcases bind_ok_inv hrest9 with ⟨v10, hstep10, hrest10⟩
  rcases v10 with ⟨x10, y10⟩
  rcases bind_ok_inv hrest10 with ⟨v11, hstep11, hrest11⟩
  rcases bind_ok_inv hrest11 with ⟨v12, hstep12, hrest12⟩
  rcases bind_ok_inv hrest12 with ⟨v13, hstep13, hrest13⟩
  rcases v13 with ⟨x13, y13⟩
  rcases bind_ok_inv hrest13 with ⟨v14, hstep14, hrest14⟩
  rcases bind_ok_inv hrest14 with ⟨v15, hstep15, hrest15⟩
  rcases bind_ok_inv hrest15 with ⟨v16, hstep16, hrest16⟩
  rcases bind_ok_inv hrest16 with ⟨v17, hstep17, hrest17⟩
  rcases v17 with ⟨x17, y17⟩
  rcases bind_ok_inv hrest17 with ⟨v18, hstep18, hrest18⟩
  rcases bind_ok_inv hrest18 with ⟨v19, hstep19, hrest19⟩
  rcases bind_ok_inv hrest19 with ⟨v20, hstep20, hrest20⟩
  rcases bind_ok_inv hrest20 with ⟨v21, hstep21, hrest21⟩
  rcases bind_ok_inv hrest21 with ⟨v22, hstep22, hrest22⟩
  rcases bind_ok_inv hrest22 with ⟨v23, hstep23, hrest23⟩
  rcases bind_ok_inv hrest23 with ⟨v24, hstep24, hrest24⟩
  rcases bind_ok_inv hrest24 with ⟨v25, hstep25, hrest25⟩
  rcases v25 with ⟨x25, y25⟩
  rcases bind_ok_inv hrest25 with ⟨v26, hstep26, hrest26⟩
  rcases bind_ok_inv hrest26 with ⟨v27, hstep27, hrest27⟩
  rcases bind_ok_inv hrest27 with ⟨v28, hstep28, hrest28⟩
  rcases bind_ok_inv hrest28 with ⟨v29, hrootIndex, hrest29⟩
  cases v29 with
  | mk rootTarget rootBack =>
    rcases bind_ok_inv hrest29 with ⟨rootBytes, hrootEncode, hrest30⟩
    rcases bind_ok_inv hrest30 with ⟨v31, hstep31, hrest31⟩
    rcases bind_ok_inv hrest31 with ⟨rootCopied, hrootCopy, hrest32⟩
    have hrootSource : v31 = Array.to_slice rootBytes := by
      simpa [lift] using hstep31.symm
    rw [hrootSource] at hrootCopy
    let base0 : Array U8 768#usize := rootBack rootCopied
    rcases bind_ok_inv hrest32 with ⟨pair_0, hindex_0, hrest33⟩
    rcases pair_0 with ⟨target_0, back_0⟩
    rcases bind_ok_inv hrest33 with ⟨frontier_0, hread_0, hrest34⟩
    rcases bind_ok_inv hrest34 with ⟨digest_0, hencode_0, hrest35⟩
    rcases bind_ok_inv hrest35 with ⟨slice_0, hlift_0, hrest36⟩
    rcases bind_ok_inv hrest36 with ⟨copied_0, hcopy_0, hrest37⟩
    have hsource_0 : slice_0 = Array.to_slice digest_0 := by
      simpa [lift] using hlift_0.symm
    rw [hsource_0] at hcopy_0
    let base_1 : Array U8 768#usize := back_0 copied_0
    rcases bind_ok_inv hrest37 with ⟨pair_1, hindex_1, hrest38⟩
    rcases pair_1 with ⟨target_1, back_1⟩
    rcases bind_ok_inv hrest38 with ⟨frontier_1, hread_1, hrest39⟩
    rcases bind_ok_inv hrest39 with ⟨digest_1, hencode_1, hrest40⟩
    rcases bind_ok_inv hrest40 with ⟨slice_1, hlift_1, hrest41⟩
    rcases bind_ok_inv hrest41 with ⟨copied_1, hcopy_1, hrest42⟩
    have hsource_1 : slice_1 = Array.to_slice digest_1 := by
      simpa [lift] using hlift_1.symm
    rw [hsource_1] at hcopy_1
    let base_2 : Array U8 768#usize := back_1 copied_1
    rcases bind_ok_inv hrest42 with ⟨pair_2, hindex_2, hrest43⟩
    rcases pair_2 with ⟨target_2, back_2⟩
    rcases bind_ok_inv hrest43 with ⟨frontier_2, hread_2, hrest44⟩
    rcases bind_ok_inv hrest44 with ⟨digest_2, hencode_2, hrest45⟩
    rcases bind_ok_inv hrest45 with ⟨slice_2, hlift_2, hrest46⟩
    rcases bind_ok_inv hrest46 with ⟨copied_2, hcopy_2, hrest47⟩
    have hsource_2 : slice_2 = Array.to_slice digest_2 := by
      simpa [lift] using hlift_2.symm
    rw [hsource_2] at hcopy_2
    let base_3 : Array U8 768#usize := back_2 copied_2
    rcases bind_ok_inv hrest47 with ⟨pair_3, hindex_3, hrest48⟩
    rcases pair_3 with ⟨target_3, back_3⟩
    rcases bind_ok_inv hrest48 with ⟨frontier_3, hread_3, hrest49⟩
    rcases bind_ok_inv hrest49 with ⟨digest_3, hencode_3, hrest50⟩
    rcases bind_ok_inv hrest50 with ⟨slice_3, hlift_3, hrest51⟩
    rcases bind_ok_inv hrest51 with ⟨copied_3, hcopy_3, hrest52⟩
    have hsource_3 : slice_3 = Array.to_slice digest_3 := by
      simpa [lift] using hlift_3.symm
    rw [hsource_3] at hcopy_3
    let base_4 : Array U8 768#usize := back_3 copied_3
    rcases bind_ok_inv hrest52 with ⟨pair_4, hindex_4, hrest53⟩
    rcases pair_4 with ⟨target_4, back_4⟩
    rcases bind_ok_inv hrest53 with ⟨frontier_4, hread_4, hrest54⟩
    rcases bind_ok_inv hrest54 with ⟨digest_4, hencode_4, hrest55⟩
    rcases bind_ok_inv hrest55 with ⟨slice_4, hlift_4, hrest56⟩
    rcases bind_ok_inv hrest56 with ⟨copied_4, hcopy_4, hrest57⟩
    have hsource_4 : slice_4 = Array.to_slice digest_4 := by
      simpa [lift] using hlift_4.symm
    rw [hsource_4] at hcopy_4
    let base_5 : Array U8 768#usize := back_4 copied_4
    rcases bind_ok_inv hrest57 with ⟨pair_5, hindex_5, hrest58⟩
    rcases pair_5 with ⟨target_5, back_5⟩
    rcases bind_ok_inv hrest58 with ⟨frontier_5, hread_5, hrest59⟩
    rcases bind_ok_inv hrest59 with ⟨digest_5, hencode_5, hrest60⟩
    rcases bind_ok_inv hrest60 with ⟨slice_5, hlift_5, hrest61⟩
    rcases bind_ok_inv hrest61 with ⟨copied_5, hcopy_5, hrest62⟩
    have hsource_5 : slice_5 = Array.to_slice digest_5 := by
      simpa [lift] using hlift_5.symm
    rw [hsource_5] at hcopy_5
    let base_6 : Array U8 768#usize := back_5 copied_5
    have hindexNorm5 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_5
        { start := 288#usize, «end» := 320#usize } = .ok (target_5, back_5) := by
      simpa [base_5] using hindex_5
    have hstart_5 : (288#usize : Usize) ≤ 320#usize := by decide
    have hend_5 : (320#usize : Usize) ≤ 768#usize := by decide
    have hlen_5 : slice_5.length = 320 - 288 := by
      rw [hsource_5]
      simp [Array.to_slice, Slice.length]
    have hbackExact_5 : (back_5 copied_5).val = base_5.val.setSlice! 288 digest_5.val := by
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact
        base_5 digest_5 target_5 copied_5 back_5
        { start := 288#usize, «end» := 320#usize } hstart_5 hend_5
        (by simpa [Array.to_slice, Slice.length] using hlen_5) hindexNorm5 hcopy_5
    have hslot_5 : ∀ k : Nat, k < 32 → (back_5 copied_5).val[288 + k]? = digest_5.val[k]? := by
      intro k hk
      rw [hbackExact_5]
      rw [List.setSlice!_getElem?_middle]
      · simp only [Nat.add_sub_cancel_left]
      · constructor
        · omega
        constructor
        · simpa [Nat.add_sub_cancel_left] using hk
        · have hb : 288 + k < 768 := by omega
          simpa using hb
    rcases bind_ok_inv hrest62 with ⟨pair_6, hindex_6, hrest63⟩
    rcases pair_6 with ⟨target_6, back_6⟩
    rcases bind_ok_inv hrest63 with ⟨frontier_6, hread_6, hrest64⟩
    rcases bind_ok_inv hrest64 with ⟨digest_6, hencode_6, hrest65⟩
    rcases bind_ok_inv hrest65 with ⟨slice_6, hlift_6, hrest66⟩
    rcases bind_ok_inv hrest66 with ⟨copied_6, hcopy_6, hrest67⟩
    have hsource_6 : slice_6 = Array.to_slice digest_6 := by
      simpa [lift] using hlift_6.symm
    rw [hsource_6] at hcopy_6
    let base_7 : Array U8 768#usize := back_6 copied_6
    have hindexNorm6 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_6
        { start := 320#usize, «end» := 352#usize } = .ok (target_6, back_6) := by
      simpa [base_6] using hindex_6
    have hstart_6 : (320#usize : Usize) ≤ 352#usize := by decide
    have hend_6 : (352#usize : Usize) ≤ 768#usize := by decide
    have hlen_6 : slice_6.length = 352 - 320 := by
      rw [hsource_6]
      simp [Array.to_slice, Slice.length]
    have hstartNat_6 : (320#usize).val = 320 := by decide
    have hframeAll_6 : ∀ q : Nat, q < 320 → (back_6 copied_6).val[q]? = base_6.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_6 (Array.to_slice digest_6) target_6 copied_6 back_6
        { start := 320#usize, «end» := 352#usize } hstart_6 hend_6
        (by simpa [Array.to_slice, Slice.length] using hlen_6) hindexNorm6 hcopy_6
        q (by change q < (320#usize).val; rw [hstartNat_6]; exact hq)
    rcases bind_ok_inv hrest67 with ⟨pair_7, hindex_7, hrest68⟩
    rcases pair_7 with ⟨target_7, back_7⟩
    rcases bind_ok_inv hrest68 with ⟨frontier_7, hread_7, hrest69⟩
    rcases bind_ok_inv hrest69 with ⟨digest_7, hencode_7, hrest70⟩
    rcases bind_ok_inv hrest70 with ⟨slice_7, hlift_7, hrest71⟩
    rcases bind_ok_inv hrest71 with ⟨copied_7, hcopy_7, hrest72⟩
    have hsource_7 : slice_7 = Array.to_slice digest_7 := by
      simpa [lift] using hlift_7.symm
    rw [hsource_7] at hcopy_7
    let base_8 : Array U8 768#usize := back_7 copied_7
    have hindexNorm7 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_7
        { start := 352#usize, «end» := 384#usize } = .ok (target_7, back_7) := by
      simpa [base_7] using hindex_7
    have hstart_7 : (352#usize : Usize) ≤ 384#usize := by decide
    have hend_7 : (384#usize : Usize) ≤ 768#usize := by decide
    have hlen_7 : slice_7.length = 384 - 352 := by
      rw [hsource_7]
      simp [Array.to_slice, Slice.length]
    have hstartNat_7 : (352#usize).val = 352 := by decide
    have hframeAll_7 : ∀ q : Nat, q < 352 → (back_7 copied_7).val[q]? = base_7.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_7 (Array.to_slice digest_7) target_7 copied_7 back_7
        { start := 352#usize, «end» := 384#usize } hstart_7 hend_7
        (by simpa [Array.to_slice, Slice.length] using hlen_7) hindexNorm7 hcopy_7
        q (by change q < (352#usize).val; rw [hstartNat_7]; exact hq)
    rcases bind_ok_inv hrest72 with ⟨pair_8, hindex_8, hrest73⟩
    rcases pair_8 with ⟨target_8, back_8⟩
    rcases bind_ok_inv hrest73 with ⟨frontier_8, hread_8, hrest74⟩
    rcases bind_ok_inv hrest74 with ⟨digest_8, hencode_8, hrest75⟩
    rcases bind_ok_inv hrest75 with ⟨slice_8, hlift_8, hrest76⟩
    rcases bind_ok_inv hrest76 with ⟨copied_8, hcopy_8, hrest77⟩
    have hsource_8 : slice_8 = Array.to_slice digest_8 := by
      simpa [lift] using hlift_8.symm
    rw [hsource_8] at hcopy_8
    let base_9 : Array U8 768#usize := back_8 copied_8
    have hindexNorm8 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_8
        { start := 384#usize, «end» := 416#usize } = .ok (target_8, back_8) := by
      simpa [base_8] using hindex_8
    have hstart_8 : (384#usize : Usize) ≤ 416#usize := by decide
    have hend_8 : (416#usize : Usize) ≤ 768#usize := by decide
    have hlen_8 : slice_8.length = 416 - 384 := by
      rw [hsource_8]
      simp [Array.to_slice, Slice.length]
    have hstartNat_8 : (384#usize).val = 384 := by decide
    have hframeAll_8 : ∀ q : Nat, q < 384 → (back_8 copied_8).val[q]? = base_8.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_8 (Array.to_slice digest_8) target_8 copied_8 back_8
        { start := 384#usize, «end» := 416#usize } hstart_8 hend_8
        (by simpa [Array.to_slice, Slice.length] using hlen_8) hindexNorm8 hcopy_8
        q (by change q < (384#usize).val; rw [hstartNat_8]; exact hq)
    rcases bind_ok_inv hrest77 with ⟨pair_9, hindex_9, hrest78⟩
    rcases pair_9 with ⟨target_9, back_9⟩
    rcases bind_ok_inv hrest78 with ⟨frontier_9, hread_9, hrest79⟩
    rcases bind_ok_inv hrest79 with ⟨digest_9, hencode_9, hrest80⟩
    rcases bind_ok_inv hrest80 with ⟨slice_9, hlift_9, hrest81⟩
    rcases bind_ok_inv hrest81 with ⟨copied_9, hcopy_9, hrest82⟩
    have hsource_9 : slice_9 = Array.to_slice digest_9 := by
      simpa [lift] using hlift_9.symm
    rw [hsource_9] at hcopy_9
    let base_10 : Array U8 768#usize := back_9 copied_9
    have hindexNorm9 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_9
        { start := 416#usize, «end» := 448#usize } = .ok (target_9, back_9) := by
      simpa [base_9] using hindex_9
    have hstart_9 : (416#usize : Usize) ≤ 448#usize := by decide
    have hend_9 : (448#usize : Usize) ≤ 768#usize := by decide
    have hlen_9 : slice_9.length = 448 - 416 := by
      rw [hsource_9]
      simp [Array.to_slice, Slice.length]
    have hstartNat_9 : (416#usize).val = 416 := by decide
    have hframeAll_9 : ∀ q : Nat, q < 416 → (back_9 copied_9).val[q]? = base_9.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_9 (Array.to_slice digest_9) target_9 copied_9 back_9
        { start := 416#usize, «end» := 448#usize } hstart_9 hend_9
        (by simpa [Array.to_slice, Slice.length] using hlen_9) hindexNorm9 hcopy_9
        q (by change q < (416#usize).val; rw [hstartNat_9]; exact hq)
    rcases bind_ok_inv hrest82 with ⟨pair_10, hindex_10, hrest83⟩
    rcases pair_10 with ⟨target_10, back_10⟩
    rcases bind_ok_inv hrest83 with ⟨frontier_10, hread_10, hrest84⟩
    rcases bind_ok_inv hrest84 with ⟨digest_10, hencode_10, hrest85⟩
    rcases bind_ok_inv hrest85 with ⟨slice_10, hlift_10, hrest86⟩
    rcases bind_ok_inv hrest86 with ⟨copied_10, hcopy_10, hrest87⟩
    have hsource_10 : slice_10 = Array.to_slice digest_10 := by
      simpa [lift] using hlift_10.symm
    rw [hsource_10] at hcopy_10
    let base_11 : Array U8 768#usize := back_10 copied_10
    have hindexNorm10 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_10
        { start := 448#usize, «end» := 480#usize } = .ok (target_10, back_10) := by
      simpa [base_10] using hindex_10
    have hstart_10 : (448#usize : Usize) ≤ 480#usize := by decide
    have hend_10 : (480#usize : Usize) ≤ 768#usize := by decide
    have hlen_10 : slice_10.length = 480 - 448 := by
      rw [hsource_10]
      simp [Array.to_slice, Slice.length]
    have hstartNat_10 : (448#usize).val = 448 := by decide
    have hframeAll_10 : ∀ q : Nat, q < 448 → (back_10 copied_10).val[q]? = base_10.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_10 (Array.to_slice digest_10) target_10 copied_10 back_10
        { start := 448#usize, «end» := 480#usize } hstart_10 hend_10
        (by simpa [Array.to_slice, Slice.length] using hlen_10) hindexNorm10 hcopy_10
        q (by change q < (448#usize).val; rw [hstartNat_10]; exact hq)
    rcases bind_ok_inv hrest87 with ⟨pair_11, hindex_11, hrest88⟩
    rcases pair_11 with ⟨target_11, back_11⟩
    rcases bind_ok_inv hrest88 with ⟨frontier_11, hread_11, hrest89⟩
    rcases bind_ok_inv hrest89 with ⟨digest_11, hencode_11, hrest90⟩
    rcases bind_ok_inv hrest90 with ⟨slice_11, hlift_11, hrest91⟩
    rcases bind_ok_inv hrest91 with ⟨copied_11, hcopy_11, hrest92⟩
    have hsource_11 : slice_11 = Array.to_slice digest_11 := by
      simpa [lift] using hlift_11.symm
    rw [hsource_11] at hcopy_11
    let base_12 : Array U8 768#usize := back_11 copied_11
    have hindexNorm11 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_11
        { start := 480#usize, «end» := 512#usize } = .ok (target_11, back_11) := by
      simpa [base_11] using hindex_11
    have hstart_11 : (480#usize : Usize) ≤ 512#usize := by decide
    have hend_11 : (512#usize : Usize) ≤ 768#usize := by decide
    have hlen_11 : slice_11.length = 512 - 480 := by
      rw [hsource_11]
      simp [Array.to_slice, Slice.length]
    have hstartNat_11 : (480#usize).val = 480 := by decide
    have hframeAll_11 : ∀ q : Nat, q < 480 → (back_11 copied_11).val[q]? = base_11.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_11 (Array.to_slice digest_11) target_11 copied_11 back_11
        { start := 480#usize, «end» := 512#usize } hstart_11 hend_11
        (by simpa [Array.to_slice, Slice.length] using hlen_11) hindexNorm11 hcopy_11
        q (by change q < (480#usize).val; rw [hstartNat_11]; exact hq)
    rcases bind_ok_inv hrest92 with ⟨pair_12, hindex_12, hrest93⟩
    rcases pair_12 with ⟨target_12, back_12⟩
    rcases bind_ok_inv hrest93 with ⟨frontier_12, hread_12, hrest94⟩
    rcases bind_ok_inv hrest94 with ⟨digest_12, hencode_12, hrest95⟩
    rcases bind_ok_inv hrest95 with ⟨slice_12, hlift_12, hrest96⟩
    rcases bind_ok_inv hrest96 with ⟨copied_12, hcopy_12, hrest97⟩
    have hsource_12 : slice_12 = Array.to_slice digest_12 := by
      simpa [lift] using hlift_12.symm
    rw [hsource_12] at hcopy_12
    let base_13 : Array U8 768#usize := back_12 copied_12
    have hindexNorm12 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_12
        { start := 512#usize, «end» := 544#usize } = .ok (target_12, back_12) := by
      simpa [base_12] using hindex_12
    have hstart_12 : (512#usize : Usize) ≤ 544#usize := by decide
    have hend_12 : (544#usize : Usize) ≤ 768#usize := by decide
    have hlen_12 : slice_12.length = 544 - 512 := by
      rw [hsource_12]
      simp [Array.to_slice, Slice.length]
    have hstartNat_12 : (512#usize).val = 512 := by decide
    have hframeAll_12 : ∀ q : Nat, q < 512 → (back_12 copied_12).val[q]? = base_12.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_12 (Array.to_slice digest_12) target_12 copied_12 back_12
        { start := 512#usize, «end» := 544#usize } hstart_12 hend_12
        (by simpa [Array.to_slice, Slice.length] using hlen_12) hindexNorm12 hcopy_12
        q (by change q < (512#usize).val; rw [hstartNat_12]; exact hq)
    rcases bind_ok_inv hrest97 with ⟨pair_13, hindex_13, hrest98⟩
    rcases pair_13 with ⟨target_13, back_13⟩
    rcases bind_ok_inv hrest98 with ⟨frontier_13, hread_13, hrest99⟩
    rcases bind_ok_inv hrest99 with ⟨digest_13, hencode_13, hrest100⟩
    rcases bind_ok_inv hrest100 with ⟨slice_13, hlift_13, hrest101⟩
    rcases bind_ok_inv hrest101 with ⟨copied_13, hcopy_13, hrest102⟩
    have hsource_13 : slice_13 = Array.to_slice digest_13 := by
      simpa [lift] using hlift_13.symm
    rw [hsource_13] at hcopy_13
    let base_14 : Array U8 768#usize := back_13 copied_13
    have hindexNorm13 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_13
        { start := 544#usize, «end» := 576#usize } = .ok (target_13, back_13) := by
      simpa [base_13] using hindex_13
    have hstart_13 : (544#usize : Usize) ≤ 576#usize := by decide
    have hend_13 : (576#usize : Usize) ≤ 768#usize := by decide
    have hlen_13 : slice_13.length = 576 - 544 := by
      rw [hsource_13]
      simp [Array.to_slice, Slice.length]
    have hstartNat_13 : (544#usize).val = 544 := by decide
    have hframeAll_13 : ∀ q : Nat, q < 544 → (back_13 copied_13).val[q]? = base_13.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_13 (Array.to_slice digest_13) target_13 copied_13 back_13
        { start := 544#usize, «end» := 576#usize } hstart_13 hend_13
        (by simpa [Array.to_slice, Slice.length] using hlen_13) hindexNorm13 hcopy_13
        q (by change q < (544#usize).val; rw [hstartNat_13]; exact hq)
    rcases bind_ok_inv hrest102 with ⟨pair_14, hindex_14, hrest103⟩
    rcases pair_14 with ⟨target_14, back_14⟩
    rcases bind_ok_inv hrest103 with ⟨frontier_14, hread_14, hrest104⟩
    rcases bind_ok_inv hrest104 with ⟨digest_14, hencode_14, hrest105⟩
    rcases bind_ok_inv hrest105 with ⟨slice_14, hlift_14, hrest106⟩
    rcases bind_ok_inv hrest106 with ⟨copied_14, hcopy_14, hrest107⟩
    have hsource_14 : slice_14 = Array.to_slice digest_14 := by
      simpa [lift] using hlift_14.symm
    rw [hsource_14] at hcopy_14
    let base_15 : Array U8 768#usize := back_14 copied_14
    have hindexNorm14 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_14
        { start := 576#usize, «end» := 608#usize } = .ok (target_14, back_14) := by
      simpa [base_14] using hindex_14
    have hstart_14 : (576#usize : Usize) ≤ 608#usize := by decide
    have hend_14 : (608#usize : Usize) ≤ 768#usize := by decide
    have hlen_14 : slice_14.length = 608 - 576 := by
      rw [hsource_14]
      simp [Array.to_slice, Slice.length]
    have hstartNat_14 : (576#usize).val = 576 := by decide
    have hframeAll_14 : ∀ q : Nat, q < 576 → (back_14 copied_14).val[q]? = base_14.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_14 (Array.to_slice digest_14) target_14 copied_14 back_14
        { start := 576#usize, «end» := 608#usize } hstart_14 hend_14
        (by simpa [Array.to_slice, Slice.length] using hlen_14) hindexNorm14 hcopy_14
        q (by change q < (576#usize).val; rw [hstartNat_14]; exact hq)
    rcases bind_ok_inv hrest107 with ⟨pair_15, hindex_15, hrest108⟩
    rcases pair_15 with ⟨target_15, back_15⟩
    rcases bind_ok_inv hrest108 with ⟨frontier_15, hread_15, hrest109⟩
    rcases bind_ok_inv hrest109 with ⟨digest_15, hencode_15, hrest110⟩
    rcases bind_ok_inv hrest110 with ⟨slice_15, hlift_15, hrest111⟩
    rcases bind_ok_inv hrest111 with ⟨copied_15, hcopy_15, hrest112⟩
    have hsource_15 : slice_15 = Array.to_slice digest_15 := by
      simpa [lift] using hlift_15.symm
    rw [hsource_15] at hcopy_15
    let base_16 : Array U8 768#usize := back_15 copied_15
    have hindexNorm15 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_15
        { start := 608#usize, «end» := 640#usize } = .ok (target_15, back_15) := by
      simpa [base_15] using hindex_15
    have hstart_15 : (608#usize : Usize) ≤ 640#usize := by decide
    have hend_15 : (640#usize : Usize) ≤ 768#usize := by decide
    have hlen_15 : slice_15.length = 640 - 608 := by
      rw [hsource_15]
      simp [Array.to_slice, Slice.length]
    have hstartNat_15 : (608#usize).val = 608 := by decide
    have hframeAll_15 : ∀ q : Nat, q < 608 → (back_15 copied_15).val[q]? = base_15.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_15 (Array.to_slice digest_15) target_15 copied_15 back_15
        { start := 608#usize, «end» := 640#usize } hstart_15 hend_15
        (by simpa [Array.to_slice, Slice.length] using hlen_15) hindexNorm15 hcopy_15
        q (by change q < (608#usize).val; rw [hstartNat_15]; exact hq)
    rcases bind_ok_inv hrest112 with ⟨pair_16, hindex_16, hrest113⟩
    rcases pair_16 with ⟨target_16, back_16⟩
    rcases bind_ok_inv hrest113 with ⟨frontier_16, hread_16, hrest114⟩
    rcases bind_ok_inv hrest114 with ⟨digest_16, hencode_16, hrest115⟩
    rcases bind_ok_inv hrest115 with ⟨slice_16, hlift_16, hrest116⟩
    rcases bind_ok_inv hrest116 with ⟨copied_16, hcopy_16, hrest117⟩
    have hsource_16 : slice_16 = Array.to_slice digest_16 := by
      simpa [lift] using hlift_16.symm
    rw [hsource_16] at hcopy_16
    let base_17 : Array U8 768#usize := back_16 copied_16
    have hindexNorm16 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_16
        { start := 640#usize, «end» := 672#usize } = .ok (target_16, back_16) := by
      simpa [base_16] using hindex_16
    have hstart_16 : (640#usize : Usize) ≤ 672#usize := by decide
    have hend_16 : (672#usize : Usize) ≤ 768#usize := by decide
    have hlen_16 : slice_16.length = 672 - 640 := by
      rw [hsource_16]
      simp [Array.to_slice, Slice.length]
    have hstartNat_16 : (640#usize).val = 640 := by decide
    have hframeAll_16 : ∀ q : Nat, q < 640 → (back_16 copied_16).val[q]? = base_16.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_16 (Array.to_slice digest_16) target_16 copied_16 back_16
        { start := 640#usize, «end» := 672#usize } hstart_16 hend_16
        (by simpa [Array.to_slice, Slice.length] using hlen_16) hindexNorm16 hcopy_16
        q (by change q < (640#usize).val; rw [hstartNat_16]; exact hq)
    rcases bind_ok_inv hrest117 with ⟨pair_17, hindex_17, hrest118⟩
    rcases pair_17 with ⟨target_17, back_17⟩
    rcases bind_ok_inv hrest118 with ⟨frontier_17, hread_17, hrest119⟩
    rcases bind_ok_inv hrest119 with ⟨digest_17, hencode_17, hrest120⟩
    rcases bind_ok_inv hrest120 with ⟨slice_17, hlift_17, hrest121⟩
    rcases bind_ok_inv hrest121 with ⟨copied_17, hcopy_17, hrest122⟩
    have hsource_17 : slice_17 = Array.to_slice digest_17 := by
      simpa [lift] using hlift_17.symm
    rw [hsource_17] at hcopy_17
    let base_18 : Array U8 768#usize := back_17 copied_17
    have hindexNorm17 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_17
        { start := 672#usize, «end» := 704#usize } = .ok (target_17, back_17) := by
      simpa [base_17] using hindex_17
    have hstart_17 : (672#usize : Usize) ≤ 704#usize := by decide
    have hend_17 : (704#usize : Usize) ≤ 768#usize := by decide
    have hlen_17 : slice_17.length = 704 - 672 := by
      rw [hsource_17]
      simp [Array.to_slice, Slice.length]
    have hstartNat_17 : (672#usize).val = 672 := by decide
    have hframeAll_17 : ∀ q : Nat, q < 672 → (back_17 copied_17).val[q]? = base_17.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_17 (Array.to_slice digest_17) target_17 copied_17 back_17
        { start := 672#usize, «end» := 704#usize } hstart_17 hend_17
        (by simpa [Array.to_slice, Slice.length] using hlen_17) hindexNorm17 hcopy_17
        q (by change q < (672#usize).val; rw [hstartNat_17]; exact hq)
    rcases bind_ok_inv hrest122 with ⟨pair_18, hindex_18, hrest123⟩
    rcases pair_18 with ⟨target_18, back_18⟩
    rcases bind_ok_inv hrest123 with ⟨frontier_18, hread_18, hrest124⟩
    rcases bind_ok_inv hrest124 with ⟨digest_18, hencode_18, hrest125⟩
    rcases bind_ok_inv hrest125 with ⟨slice_18, hlift_18, hrest126⟩
    rcases bind_ok_inv hrest126 with ⟨copied_18, hcopy_18, hrest127⟩
    have hsource_18 : slice_18 = Array.to_slice digest_18 := by
      simpa [lift] using hlift_18.symm
    rw [hsource_18] at hcopy_18
    let base_19 : Array U8 768#usize := back_18 copied_18
    have hindexNorm18 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_18
        { start := 704#usize, «end» := 736#usize } = .ok (target_18, back_18) := by
      simpa [base_18] using hindex_18
    have hstart_18 : (704#usize : Usize) ≤ 736#usize := by decide
    have hend_18 : (736#usize : Usize) ≤ 768#usize := by decide
    have hlen_18 : slice_18.length = 736 - 704 := by
      rw [hsource_18]
      simp [Array.to_slice, Slice.length]
    have hstartNat_18 : (704#usize).val = 704 := by decide
    have hframeAll_18 : ∀ q : Nat, q < 704 → (back_18 copied_18).val[q]? = base_18.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_18 (Array.to_slice digest_18) target_18 copied_18 back_18
        { start := 704#usize, «end» := 736#usize } hstart_18 hend_18
        (by simpa [Array.to_slice, Slice.length] using hlen_18) hindexNorm18 hcopy_18
        q (by change q < (704#usize).val; rw [hstartNat_18]; exact hq)
    rcases bind_ok_inv hrest127 with ⟨pair_19, hindex_19, hrest128⟩
    rcases pair_19 with ⟨target_19, back_19⟩
    rcases bind_ok_inv hrest128 with ⟨frontier_19, hread_19, hrest129⟩
    rcases bind_ok_inv hrest129 with ⟨digest_19, hencode_19, hrest130⟩
    rcases bind_ok_inv hrest130 with ⟨slice_19, hlift_19, hrest131⟩
    rcases bind_ok_inv hrest131 with ⟨copied_19, hcopy_19, hrest132⟩
    have hsource_19 : slice_19 = Array.to_slice digest_19 := by
      simpa [lift] using hlift_19.symm
    rw [hsource_19] at hcopy_19
    let base_20 : Array U8 768#usize := back_19 copied_19
    have hindexNorm19 : core.array.Array.index_mut
        (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base_19
        { start := 736#usize, «end» := 768#usize } = .ok (target_19, back_19) := by
      simpa [base_19] using hindex_19
    have hstart_19 : (736#usize : Usize) ≤ 768#usize := by decide
    have hend_19 : (768#usize : Usize) ≤ 768#usize := by decide
    have hlen_19 : slice_19.length = 768 - 736 := by
      rw [hsource_19]
      simp [Array.to_slice, Slice.length]
    have hstartNat_19 : (736#usize).val = 736 := by decide
    have hframeAll_19 : ∀ q : Nat, q < 736 → (back_19 copied_19).val[q]? = base_19.val[q]? := by
      intro q hq
      exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
        base_19 (Array.to_slice digest_19) target_19 copied_19 back_19
        { start := 736#usize, «end» := 768#usize } hstart_19 hend_19
        (by simpa [Array.to_slice, Slice.length] using hlen_19) hindexNorm19 hcopy_19
        q (by change q < (736#usize).val; rw [hstartNat_19]; exact hq)
    have hfinal : base_20 = out := by
      exact Result.ok.inj hrest132
    refine ⟨frontier_5, digest_5, hread_5, hencode_5, ?_⟩
    intro k hk
    calc
      out.val[288 + k]? = base_20.val[288 + k]? := by simpa [hfinal]
      _ = base_19.val[288 + k]? := hframeAll_19 (288 + k) (by omega)
      _ = base_18.val[288 + k]? := hframeAll_18 (288 + k) (by omega)
      _ = base_17.val[288 + k]? := hframeAll_17 (288 + k) (by omega)
      _ = base_16.val[288 + k]? := hframeAll_16 (288 + k) (by omega)
      _ = base_15.val[288 + k]? := hframeAll_15 (288 + k) (by omega)
      _ = base_14.val[288 + k]? := hframeAll_14 (288 + k) (by omega)
      _ = base_13.val[288 + k]? := hframeAll_13 (288 + k) (by omega)
      _ = base_12.val[288 + k]? := hframeAll_12 (288 + k) (by omega)
      _ = base_11.val[288 + k]? := hframeAll_11 (288 + k) (by omega)
      _ = base_10.val[288 + k]? := hframeAll_10 (288 + k) (by omega)
      _ = base_9.val[288 + k]? := hframeAll_9 (288 + k) (by omega)
      _ = base_8.val[288 + k]? := hframeAll_8 (288 + k) (by omega)
      _ = base_7.val[288 + k]? := hframeAll_7 (288 + k) (by omega)
      _ = base_6.val[288 + k]? := hframeAll_6 (288 + k) (by omega)
      _ = (back_5 copied_5).val[288 + k]? := by rfl
      _ = digest_5.val[k]? := hslot_5 k hk

#print axioms successful_tail_preserves_frontier_5_bytes
end AspisR1PairForestLaneEncoderTailActualRootBlock
