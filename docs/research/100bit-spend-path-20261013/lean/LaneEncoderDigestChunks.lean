import AspisR1PairForestLaneEncoderTailSourceCut.Funs
import AspisR1PairForestLaneEncoderTailRangeWriteFrameV5
import LaneEncoderCursorBytes
import LaneEncoderM31FieldBytes
import Aeneas.Std
set_option autoImplicit false
namespace AspisR1PairForestLaneEncoderTailActualDigestChunks
open Aeneas Aeneas.Std Result AspisR1PairForestLaneEncoderTailSourceCut

structure DigestChunkProjection (digest : Array M31 8#usize) (out : Array U8 32#usize) : Prop where
  chunk0 : ∃ value : M31, ∃ bytes : Array U8 4#usize,
    Array.index_usize digest 0#usize = .ok value ∧
    M31.to_le_bytes value = .ok bytes ∧
    ∀ k : Nat, k < 4 → out.val[0 + k]? = bytes.val[k]?
  chunk1 : ∃ value : M31, ∃ bytes : Array U8 4#usize,
    Array.index_usize digest 1#usize = .ok value ∧
    M31.to_le_bytes value = .ok bytes ∧
    ∀ k : Nat, k < 4 → out.val[4 + k]? = bytes.val[k]?
  chunk2 : ∃ value : M31, ∃ bytes : Array U8 4#usize,
    Array.index_usize digest 2#usize = .ok value ∧
    M31.to_le_bytes value = .ok bytes ∧
    ∀ k : Nat, k < 4 → out.val[8 + k]? = bytes.val[k]?
  chunk3 : ∃ value : M31, ∃ bytes : Array U8 4#usize,
    Array.index_usize digest 3#usize = .ok value ∧
    M31.to_le_bytes value = .ok bytes ∧
    ∀ k : Nat, k < 4 → out.val[12 + k]? = bytes.val[k]?
  chunk4 : ∃ value : M31, ∃ bytes : Array U8 4#usize,
    Array.index_usize digest 4#usize = .ok value ∧
    M31.to_le_bytes value = .ok bytes ∧
    ∀ k : Nat, k < 4 → out.val[16 + k]? = bytes.val[k]?
  chunk5 : ∃ value : M31, ∃ bytes : Array U8 4#usize,
    Array.index_usize digest 5#usize = .ok value ∧
    M31.to_le_bytes value = .ok bytes ∧
    ∀ k : Nat, k < 4 → out.val[20 + k]? = bytes.val[k]?
  chunk6 : ∃ value : M31, ∃ bytes : Array U8 4#usize,
    Array.index_usize digest 6#usize = .ok value ∧
    M31.to_le_bytes value = .ok bytes ∧
    ∀ k : Nat, k < 4 → out.val[24 + k]? = bytes.val[k]?
  chunk7 : ∃ value : M31, ∃ bytes : Array U8 4#usize,
    Array.index_usize digest 7#usize = .ok value ∧
    M31.to_le_bytes value = .ok bytes ∧
    ∀ k : Nat, k < 4 → out.val[28 + k]? = bytes.val[k]?

theorem successful_digest_chunks
    (digest : Array M31 8#usize) (out : Array U8 32#usize)
    (hok : encode_digest_canonical digest = .ok out) :
    DigestChunkProjection digest out := by
  have h := hok
  unfold encode_digest_canonical at h
  let hrest0 := h
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest0 with ⟨pair0, hindex0, hrest1⟩
  rcases pair0 with ⟨target0, back0⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest1 with ⟨m0, hread0, hrest2⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest2 with ⟨a0, hencode0, hrest3⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest3 with ⟨s1, hslice0, hrest4⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest4 with ⟨copied0, hcopy0, hrest5⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest5 with ⟨pair1, hindex1, hrest6⟩
  rcases pair1 with ⟨target1, back1⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest6 with ⟨m1, hread1, hrest7⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest7 with ⟨a1, hencode1, hrest8⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest8 with ⟨s4, hslice1, hrest9⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest9 with ⟨copied1, hcopy1, hrest10⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest10 with ⟨pair2, hindex2, hrest11⟩
  rcases pair2 with ⟨target2, back2⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest11 with ⟨m2, hread2, hrest12⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest12 with ⟨a2, hencode2, hrest13⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest13 with ⟨s7, hslice2, hrest14⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest14 with ⟨copied2, hcopy2, hrest15⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest15 with ⟨pair3, hindex3, hrest16⟩
  rcases pair3 with ⟨target3, back3⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest16 with ⟨m3, hread3, hrest17⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest17 with ⟨a3, hencode3, hrest18⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest18 with ⟨s10, hslice3, hrest19⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest19 with ⟨copied3, hcopy3, hrest20⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest20 with ⟨pair4, hindex4, hrest21⟩
  rcases pair4 with ⟨target4, back4⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest21 with ⟨m4, hread4, hrest22⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest22 with ⟨a4, hencode4, hrest23⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest23 with ⟨s13, hslice4, hrest24⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest24 with ⟨copied4, hcopy4, hrest25⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest25 with ⟨pair5, hindex5, hrest26⟩
  rcases pair5 with ⟨target5, back5⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest26 with ⟨m5, hread5, hrest27⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest27 with ⟨a5, hencode5, hrest28⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest28 with ⟨s16, hslice5, hrest29⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest29 with ⟨copied5, hcopy5, hrest30⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest30 with ⟨pair6, hindex6, hrest31⟩
  rcases pair6 with ⟨target6, back6⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest31 with ⟨m6, hread6, hrest32⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest32 with ⟨a6, hencode6, hrest33⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest33 with ⟨s19, hslice6, hrest34⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest34 with ⟨copied6, hcopy6, hrest35⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest35 with ⟨pair7, hindex7, hrest36⟩
  rcases pair7 with ⟨target7, back7⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest36 with ⟨m7, hread7, hrest37⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest37 with ⟨a7, hencode7, hrest38⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest38 with ⟨s22, hslice7, hrest39⟩
  rcases AspisR1PairForestLaneEncoderTailActualRootBlock.bind_ok_inv hrest39 with ⟨copied7, hcopy7, hrest40⟩
  have hfinal : back7 copied7 = out := Result.ok.inj hrest40
  have hsource0 : s1 = Array.to_slice a0 := by
    simpa [lift] using hslice0.symm
  rw [hsource0] at hcopy0
  let base0 : Array U8 32#usize := Array.repeat 32#usize 0#u8
  have hindexNorm0 : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base0
      { start := 0#usize, «end» := 4#usize } = .ok (target0, back0) := by
    simpa [base0] using hindex0
  have hstart0 : (0#usize : Usize) ≤ 4#usize := by decide
  have hend0 : (4#usize : Usize) ≤ 32#usize := by decide
  have hlen0 : (Array.to_slice a0).length = 4 - 0 := by
    simp [Array.to_slice, Slice.length]
  have hbackExact0 : (back0 copied0).val = base0.val.setSlice! 0 a0.val := by
    exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact
      base0 a0 target0 copied0 back0
      { start := 0#usize, «end» := 4#usize }
      hstart0 hend0
      (by simpa [Array.to_slice, Slice.length] using hlen0)
      hindexNorm0 hcopy0
  have hstartNat0 : (0#usize).val = 0 := by decide
  have hslot0 : ∀ k : Nat, k < 4 →
      (back0 copied0).val[0 + k]? = a0.val[k]? := by
    intro k hk
    rw [hbackExact0]
    rw [List.setSlice!_getElem?_middle]
    · simp only [hstartNat0, Nat.add_sub_cancel_left]
    · constructor
      · change (0#usize).val ≤ 0 + k
        rw [hstartNat0]
        omega
      constructor
      · simpa [hstartNat0, Nat.add_sub_cancel_left] using hk
      · have hb : 0 + k < 32 := by omega
        simpa using hb
  have hsource1 : s4 = Array.to_slice a1 := by
    simpa [lift] using hslice1.symm
  rw [hsource1] at hcopy1
  let base1 : Array U8 32#usize := back0 copied0
  have hindexNorm1 : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base1
      { start := 4#usize, «end» := 8#usize } = .ok (target1, back1) := by
    simpa [base1] using hindex1
  have hstart1 : (4#usize : Usize) ≤ 8#usize := by decide
  have hend1 : (8#usize : Usize) ≤ 32#usize := by decide
  have hlen1 : (Array.to_slice a1).length = 8 - 4 := by
    simp [Array.to_slice, Slice.length]
  have hbackExact1 : (back1 copied1).val = base1.val.setSlice! 4 a1.val := by
    exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact
      base1 a1 target1 copied1 back1
      { start := 4#usize, «end» := 8#usize }
      hstart1 hend1
      (by simpa [Array.to_slice, Slice.length] using hlen1)
      hindexNorm1 hcopy1
  have hstartNat1 : (4#usize).val = 4 := by decide
  have hslot1 : ∀ k : Nat, k < 4 →
      (back1 copied1).val[4 + k]? = a1.val[k]? := by
    intro k hk
    rw [hbackExact1]
    rw [List.setSlice!_getElem?_middle]
    · simp only [hstartNat1, Nat.add_sub_cancel_left]
    · constructor
      · change (4#usize).val ≤ 4 + k
        rw [hstartNat1]
        omega
      constructor
      · simpa [hstartNat1, Nat.add_sub_cancel_left] using hk
      · have hb : 4 + k < 32 := by omega
        simpa using hb
  have hsource2 : s7 = Array.to_slice a2 := by
    simpa [lift] using hslice2.symm
  rw [hsource2] at hcopy2
  let base2 : Array U8 32#usize := back1 copied1
  have hindexNorm2 : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base2
      { start := 8#usize, «end» := 12#usize } = .ok (target2, back2) := by
    simpa [base2] using hindex2
  have hstart2 : (8#usize : Usize) ≤ 12#usize := by decide
  have hend2 : (12#usize : Usize) ≤ 32#usize := by decide
  have hlen2 : (Array.to_slice a2).length = 12 - 8 := by
    simp [Array.to_slice, Slice.length]
  have hbackExact2 : (back2 copied2).val = base2.val.setSlice! 8 a2.val := by
    exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact
      base2 a2 target2 copied2 back2
      { start := 8#usize, «end» := 12#usize }
      hstart2 hend2
      (by simpa [Array.to_slice, Slice.length] using hlen2)
      hindexNorm2 hcopy2
  have hstartNat2 : (8#usize).val = 8 := by decide
  have hslot2 : ∀ k : Nat, k < 4 →
      (back2 copied2).val[8 + k]? = a2.val[k]? := by
    intro k hk
    rw [hbackExact2]
    rw [List.setSlice!_getElem?_middle]
    · simp only [hstartNat2, Nat.add_sub_cancel_left]
    · constructor
      · change (8#usize).val ≤ 8 + k
        rw [hstartNat2]
        omega
      constructor
      · simpa [hstartNat2, Nat.add_sub_cancel_left] using hk
      · have hb : 8 + k < 32 := by omega
        simpa using hb
  have hsource3 : s10 = Array.to_slice a3 := by
    simpa [lift] using hslice3.symm
  rw [hsource3] at hcopy3
  let base3 : Array U8 32#usize := back2 copied2
  have hindexNorm3 : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base3
      { start := 12#usize, «end» := 16#usize } = .ok (target3, back3) := by
    simpa [base3] using hindex3
  have hstart3 : (12#usize : Usize) ≤ 16#usize := by decide
  have hend3 : (16#usize : Usize) ≤ 32#usize := by decide
  have hlen3 : (Array.to_slice a3).length = 16 - 12 := by
    simp [Array.to_slice, Slice.length]
  have hbackExact3 : (back3 copied3).val = base3.val.setSlice! 12 a3.val := by
    exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact
      base3 a3 target3 copied3 back3
      { start := 12#usize, «end» := 16#usize }
      hstart3 hend3
      (by simpa [Array.to_slice, Slice.length] using hlen3)
      hindexNorm3 hcopy3
  have hstartNat3 : (12#usize).val = 12 := by decide
  have hslot3 : ∀ k : Nat, k < 4 →
      (back3 copied3).val[12 + k]? = a3.val[k]? := by
    intro k hk
    rw [hbackExact3]
    rw [List.setSlice!_getElem?_middle]
    · simp only [hstartNat3, Nat.add_sub_cancel_left]
    · constructor
      · change (12#usize).val ≤ 12 + k
        rw [hstartNat3]
        omega
      constructor
      · simpa [hstartNat3, Nat.add_sub_cancel_left] using hk
      · have hb : 12 + k < 32 := by omega
        simpa using hb
  have hsource4 : s13 = Array.to_slice a4 := by
    simpa [lift] using hslice4.symm
  rw [hsource4] at hcopy4
  let base4 : Array U8 32#usize := back3 copied3
  have hindexNorm4 : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base4
      { start := 16#usize, «end» := 20#usize } = .ok (target4, back4) := by
    simpa [base4] using hindex4
  have hstart4 : (16#usize : Usize) ≤ 20#usize := by decide
  have hend4 : (20#usize : Usize) ≤ 32#usize := by decide
  have hlen4 : (Array.to_slice a4).length = 20 - 16 := by
    simp [Array.to_slice, Slice.length]
  have hbackExact4 : (back4 copied4).val = base4.val.setSlice! 16 a4.val := by
    exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact
      base4 a4 target4 copied4 back4
      { start := 16#usize, «end» := 20#usize }
      hstart4 hend4
      (by simpa [Array.to_slice, Slice.length] using hlen4)
      hindexNorm4 hcopy4
  have hstartNat4 : (16#usize).val = 16 := by decide
  have hslot4 : ∀ k : Nat, k < 4 →
      (back4 copied4).val[16 + k]? = a4.val[k]? := by
    intro k hk
    rw [hbackExact4]
    rw [List.setSlice!_getElem?_middle]
    · simp only [hstartNat4, Nat.add_sub_cancel_left]
    · constructor
      · change (16#usize).val ≤ 16 + k
        rw [hstartNat4]
        omega
      constructor
      · simpa [hstartNat4, Nat.add_sub_cancel_left] using hk
      · have hb : 16 + k < 32 := by omega
        simpa using hb
  have hsource5 : s16 = Array.to_slice a5 := by
    simpa [lift] using hslice5.symm
  rw [hsource5] at hcopy5
  let base5 : Array U8 32#usize := back4 copied4
  have hindexNorm5 : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base5
      { start := 20#usize, «end» := 24#usize } = .ok (target5, back5) := by
    simpa [base5] using hindex5
  have hstart5 : (20#usize : Usize) ≤ 24#usize := by decide
  have hend5 : (24#usize : Usize) ≤ 32#usize := by decide
  have hlen5 : (Array.to_slice a5).length = 24 - 20 := by
    simp [Array.to_slice, Slice.length]
  have hbackExact5 : (back5 copied5).val = base5.val.setSlice! 20 a5.val := by
    exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact
      base5 a5 target5 copied5 back5
      { start := 20#usize, «end» := 24#usize }
      hstart5 hend5
      (by simpa [Array.to_slice, Slice.length] using hlen5)
      hindexNorm5 hcopy5
  have hstartNat5 : (20#usize).val = 20 := by decide
  have hslot5 : ∀ k : Nat, k < 4 →
      (back5 copied5).val[20 + k]? = a5.val[k]? := by
    intro k hk
    rw [hbackExact5]
    rw [List.setSlice!_getElem?_middle]
    · simp only [hstartNat5, Nat.add_sub_cancel_left]
    · constructor
      · change (20#usize).val ≤ 20 + k
        rw [hstartNat5]
        omega
      constructor
      · simpa [hstartNat5, Nat.add_sub_cancel_left] using hk
      · have hb : 20 + k < 32 := by omega
        simpa using hb
  have hsource6 : s19 = Array.to_slice a6 := by
    simpa [lift] using hslice6.symm
  rw [hsource6] at hcopy6
  let base6 : Array U8 32#usize := back5 copied5
  have hindexNorm6 : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base6
      { start := 24#usize, «end» := 28#usize } = .ok (target6, back6) := by
    simpa [base6] using hindex6
  have hstart6 : (24#usize : Usize) ≤ 28#usize := by decide
  have hend6 : (28#usize : Usize) ≤ 32#usize := by decide
  have hlen6 : (Array.to_slice a6).length = 28 - 24 := by
    simp [Array.to_slice, Slice.length]
  have hbackExact6 : (back6 copied6).val = base6.val.setSlice! 24 a6.val := by
    exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact
      base6 a6 target6 copied6 back6
      { start := 24#usize, «end» := 28#usize }
      hstart6 hend6
      (by simpa [Array.to_slice, Slice.length] using hlen6)
      hindexNorm6 hcopy6
  have hstartNat6 : (24#usize).val = 24 := by decide
  have hslot6 : ∀ k : Nat, k < 4 →
      (back6 copied6).val[24 + k]? = a6.val[k]? := by
    intro k hk
    rw [hbackExact6]
    rw [List.setSlice!_getElem?_middle]
    · simp only [hstartNat6, Nat.add_sub_cancel_left]
    · constructor
      · change (24#usize).val ≤ 24 + k
        rw [hstartNat6]
        omega
      constructor
      · simpa [hstartNat6, Nat.add_sub_cancel_left] using hk
      · have hb : 24 + k < 32 := by omega
        simpa using hb
  have hsource7 : s22 = Array.to_slice a7 := by
    simpa [lift] using hslice7.symm
  rw [hsource7] at hcopy7
  let base7 : Array U8 32#usize := back6 copied6
  have hindexNorm7 : core.array.Array.index_mut
      (core.ops.index.IndexMutSlice (core.slice.index.SliceIndexRangeUsizeSlice U8)) base7
      { start := 28#usize, «end» := 32#usize } = .ok (target7, back7) := by
    simpa [base7] using hindex7
  have hstart7 : (28#usize : Usize) ≤ 32#usize := by decide
  have hend7 : (32#usize : Usize) ≤ 32#usize := by decide
  have hlen7 : (Array.to_slice a7).length = 32 - 28 := by
    simp [Array.to_slice, Slice.length]
  have hbackExact7 : (back7 copied7).val = base7.val.setSlice! 28 a7.val := by
    exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_back_exact
      base7 a7 target7 copied7 back7
      { start := 28#usize, «end» := 32#usize }
      hstart7 hend7
      (by simpa [Array.to_slice, Slice.length] using hlen7)
      hindexNorm7 hcopy7
  have hstartNat7 : (28#usize).val = 28 := by decide
  have hslot7 : ∀ k : Nat, k < 4 →
      (back7 copied7).val[28 + k]? = a7.val[k]? := by
    intro k hk
    rw [hbackExact7]
    rw [List.setSlice!_getElem?_middle]
    · simp only [hstartNat7, Nat.add_sub_cancel_left]
    · constructor
      · change (28#usize).val ≤ 28 + k
        rw [hstartNat7]
        omega
      constructor
      · simpa [hstartNat7, Nat.add_sub_cancel_left] using hk
      · have hb : 28 + k < 32 := by omega
        simpa using hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨m0, a0, hread0, hencode0, ?_⟩
    intro k hk
    calc
      out.val[0 + k]? = (back7 copied7).val[0 + k]? := by rw [hfinal]
      _ = base7.val[0 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base7 (Array.to_slice a7) target7 copied7 back7
          { start := 28#usize, «end» := 32#usize }
          hstart7 hend7
          (by simpa [Array.to_slice, Slice.length] using hlen7)
          hindexNorm7 hcopy7 (0 + k) (by change 0 + k < (28#usize).val; rw [hstartNat7]; omega)
      _ = (back6 copied6).val[0 + k]? := by rfl
      _ = base6.val[0 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base6 (Array.to_slice a6) target6 copied6 back6
          { start := 24#usize, «end» := 28#usize }
          hstart6 hend6
          (by simpa [Array.to_slice, Slice.length] using hlen6)
          hindexNorm6 hcopy6 (0 + k) (by change 0 + k < (24#usize).val; rw [hstartNat6]; omega)
      _ = (back5 copied5).val[0 + k]? := by rfl
      _ = base5.val[0 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base5 (Array.to_slice a5) target5 copied5 back5
          { start := 20#usize, «end» := 24#usize }
          hstart5 hend5
          (by simpa [Array.to_slice, Slice.length] using hlen5)
          hindexNorm5 hcopy5 (0 + k) (by change 0 + k < (20#usize).val; rw [hstartNat5]; omega)
      _ = (back4 copied4).val[0 + k]? := by rfl
      _ = base4.val[0 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base4 (Array.to_slice a4) target4 copied4 back4
          { start := 16#usize, «end» := 20#usize }
          hstart4 hend4
          (by simpa [Array.to_slice, Slice.length] using hlen4)
          hindexNorm4 hcopy4 (0 + k) (by change 0 + k < (16#usize).val; rw [hstartNat4]; omega)
      _ = (back3 copied3).val[0 + k]? := by rfl
      _ = base3.val[0 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base3 (Array.to_slice a3) target3 copied3 back3
          { start := 12#usize, «end» := 16#usize }
          hstart3 hend3
          (by simpa [Array.to_slice, Slice.length] using hlen3)
          hindexNorm3 hcopy3 (0 + k) (by change 0 + k < (12#usize).val; rw [hstartNat3]; omega)
      _ = (back2 copied2).val[0 + k]? := by rfl
      _ = base2.val[0 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base2 (Array.to_slice a2) target2 copied2 back2
          { start := 8#usize, «end» := 12#usize }
          hstart2 hend2
          (by simpa [Array.to_slice, Slice.length] using hlen2)
          hindexNorm2 hcopy2 (0 + k) (by change 0 + k < (8#usize).val; rw [hstartNat2]; omega)
      _ = (back1 copied1).val[0 + k]? := by rfl
      _ = base1.val[0 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base1 (Array.to_slice a1) target1 copied1 back1
          { start := 4#usize, «end» := 8#usize }
          hstart1 hend1
          (by simpa [Array.to_slice, Slice.length] using hlen1)
          hindexNorm1 hcopy1 (0 + k) (by change 0 + k < (4#usize).val; rw [hstartNat1]; omega)
      _ = (back0 copied0).val[0 + k]? := by rfl
      _ = a0.val[k]? := by
        have := hslot0 k hk
        simpa using this
  · refine ⟨m1, a1, hread1, hencode1, ?_⟩
    intro k hk
    calc
      out.val[4 + k]? = (back7 copied7).val[4 + k]? := by rw [hfinal]
      _ = base7.val[4 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base7 (Array.to_slice a7) target7 copied7 back7
          { start := 28#usize, «end» := 32#usize }
          hstart7 hend7
          (by simpa [Array.to_slice, Slice.length] using hlen7)
          hindexNorm7 hcopy7 (4 + k) (by change 4 + k < (28#usize).val; rw [hstartNat7]; omega)
      _ = (back6 copied6).val[4 + k]? := by rfl
      _ = base6.val[4 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base6 (Array.to_slice a6) target6 copied6 back6
          { start := 24#usize, «end» := 28#usize }
          hstart6 hend6
          (by simpa [Array.to_slice, Slice.length] using hlen6)
          hindexNorm6 hcopy6 (4 + k) (by change 4 + k < (24#usize).val; rw [hstartNat6]; omega)
      _ = (back5 copied5).val[4 + k]? := by rfl
      _ = base5.val[4 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base5 (Array.to_slice a5) target5 copied5 back5
          { start := 20#usize, «end» := 24#usize }
          hstart5 hend5
          (by simpa [Array.to_slice, Slice.length] using hlen5)
          hindexNorm5 hcopy5 (4 + k) (by change 4 + k < (20#usize).val; rw [hstartNat5]; omega)
      _ = (back4 copied4).val[4 + k]? := by rfl
      _ = base4.val[4 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base4 (Array.to_slice a4) target4 copied4 back4
          { start := 16#usize, «end» := 20#usize }
          hstart4 hend4
          (by simpa [Array.to_slice, Slice.length] using hlen4)
          hindexNorm4 hcopy4 (4 + k) (by change 4 + k < (16#usize).val; rw [hstartNat4]; omega)
      _ = (back3 copied3).val[4 + k]? := by rfl
      _ = base3.val[4 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base3 (Array.to_slice a3) target3 copied3 back3
          { start := 12#usize, «end» := 16#usize }
          hstart3 hend3
          (by simpa [Array.to_slice, Slice.length] using hlen3)
          hindexNorm3 hcopy3 (4 + k) (by change 4 + k < (12#usize).val; rw [hstartNat3]; omega)
      _ = (back2 copied2).val[4 + k]? := by rfl
      _ = base2.val[4 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base2 (Array.to_slice a2) target2 copied2 back2
          { start := 8#usize, «end» := 12#usize }
          hstart2 hend2
          (by simpa [Array.to_slice, Slice.length] using hlen2)
          hindexNorm2 hcopy2 (4 + k) (by change 4 + k < (8#usize).val; rw [hstartNat2]; omega)
      _ = (back1 copied1).val[4 + k]? := by rfl
      _ = a1.val[k]? := by
        have := hslot1 k hk
        simpa using this
  · refine ⟨m2, a2, hread2, hencode2, ?_⟩
    intro k hk
    calc
      out.val[8 + k]? = (back7 copied7).val[8 + k]? := by rw [hfinal]
      _ = base7.val[8 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base7 (Array.to_slice a7) target7 copied7 back7
          { start := 28#usize, «end» := 32#usize }
          hstart7 hend7
          (by simpa [Array.to_slice, Slice.length] using hlen7)
          hindexNorm7 hcopy7 (8 + k) (by change 8 + k < (28#usize).val; rw [hstartNat7]; omega)
      _ = (back6 copied6).val[8 + k]? := by rfl
      _ = base6.val[8 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base6 (Array.to_slice a6) target6 copied6 back6
          { start := 24#usize, «end» := 28#usize }
          hstart6 hend6
          (by simpa [Array.to_slice, Slice.length] using hlen6)
          hindexNorm6 hcopy6 (8 + k) (by change 8 + k < (24#usize).val; rw [hstartNat6]; omega)
      _ = (back5 copied5).val[8 + k]? := by rfl
      _ = base5.val[8 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base5 (Array.to_slice a5) target5 copied5 back5
          { start := 20#usize, «end» := 24#usize }
          hstart5 hend5
          (by simpa [Array.to_slice, Slice.length] using hlen5)
          hindexNorm5 hcopy5 (8 + k) (by change 8 + k < (20#usize).val; rw [hstartNat5]; omega)
      _ = (back4 copied4).val[8 + k]? := by rfl
      _ = base4.val[8 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base4 (Array.to_slice a4) target4 copied4 back4
          { start := 16#usize, «end» := 20#usize }
          hstart4 hend4
          (by simpa [Array.to_slice, Slice.length] using hlen4)
          hindexNorm4 hcopy4 (8 + k) (by change 8 + k < (16#usize).val; rw [hstartNat4]; omega)
      _ = (back3 copied3).val[8 + k]? := by rfl
      _ = base3.val[8 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base3 (Array.to_slice a3) target3 copied3 back3
          { start := 12#usize, «end» := 16#usize }
          hstart3 hend3
          (by simpa [Array.to_slice, Slice.length] using hlen3)
          hindexNorm3 hcopy3 (8 + k) (by change 8 + k < (12#usize).val; rw [hstartNat3]; omega)
      _ = (back2 copied2).val[8 + k]? := by rfl
      _ = a2.val[k]? := by
        have := hslot2 k hk
        simpa using this
  · refine ⟨m3, a3, hread3, hencode3, ?_⟩
    intro k hk
    calc
      out.val[12 + k]? = (back7 copied7).val[12 + k]? := by rw [hfinal]
      _ = base7.val[12 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base7 (Array.to_slice a7) target7 copied7 back7
          { start := 28#usize, «end» := 32#usize }
          hstart7 hend7
          (by simpa [Array.to_slice, Slice.length] using hlen7)
          hindexNorm7 hcopy7 (12 + k) (by change 12 + k < (28#usize).val; rw [hstartNat7]; omega)
      _ = (back6 copied6).val[12 + k]? := by rfl
      _ = base6.val[12 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base6 (Array.to_slice a6) target6 copied6 back6
          { start := 24#usize, «end» := 28#usize }
          hstart6 hend6
          (by simpa [Array.to_slice, Slice.length] using hlen6)
          hindexNorm6 hcopy6 (12 + k) (by change 12 + k < (24#usize).val; rw [hstartNat6]; omega)
      _ = (back5 copied5).val[12 + k]? := by rfl
      _ = base5.val[12 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base5 (Array.to_slice a5) target5 copied5 back5
          { start := 20#usize, «end» := 24#usize }
          hstart5 hend5
          (by simpa [Array.to_slice, Slice.length] using hlen5)
          hindexNorm5 hcopy5 (12 + k) (by change 12 + k < (20#usize).val; rw [hstartNat5]; omega)
      _ = (back4 copied4).val[12 + k]? := by rfl
      _ = base4.val[12 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base4 (Array.to_slice a4) target4 copied4 back4
          { start := 16#usize, «end» := 20#usize }
          hstart4 hend4
          (by simpa [Array.to_slice, Slice.length] using hlen4)
          hindexNorm4 hcopy4 (12 + k) (by change 12 + k < (16#usize).val; rw [hstartNat4]; omega)
      _ = (back3 copied3).val[12 + k]? := by rfl
      _ = a3.val[k]? := by
        have := hslot3 k hk
        simpa using this
  · refine ⟨m4, a4, hread4, hencode4, ?_⟩
    intro k hk
    calc
      out.val[16 + k]? = (back7 copied7).val[16 + k]? := by rw [hfinal]
      _ = base7.val[16 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base7 (Array.to_slice a7) target7 copied7 back7
          { start := 28#usize, «end» := 32#usize }
          hstart7 hend7
          (by simpa [Array.to_slice, Slice.length] using hlen7)
          hindexNorm7 hcopy7 (16 + k) (by change 16 + k < (28#usize).val; rw [hstartNat7]; omega)
      _ = (back6 copied6).val[16 + k]? := by rfl
      _ = base6.val[16 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base6 (Array.to_slice a6) target6 copied6 back6
          { start := 24#usize, «end» := 28#usize }
          hstart6 hend6
          (by simpa [Array.to_slice, Slice.length] using hlen6)
          hindexNorm6 hcopy6 (16 + k) (by change 16 + k < (24#usize).val; rw [hstartNat6]; omega)
      _ = (back5 copied5).val[16 + k]? := by rfl
      _ = base5.val[16 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base5 (Array.to_slice a5) target5 copied5 back5
          { start := 20#usize, «end» := 24#usize }
          hstart5 hend5
          (by simpa [Array.to_slice, Slice.length] using hlen5)
          hindexNorm5 hcopy5 (16 + k) (by change 16 + k < (20#usize).val; rw [hstartNat5]; omega)
      _ = (back4 copied4).val[16 + k]? := by rfl
      _ = a4.val[k]? := by
        have := hslot4 k hk
        simpa using this
  · refine ⟨m5, a5, hread5, hencode5, ?_⟩
    intro k hk
    calc
      out.val[20 + k]? = (back7 copied7).val[20 + k]? := by rw [hfinal]
      _ = base7.val[20 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base7 (Array.to_slice a7) target7 copied7 back7
          { start := 28#usize, «end» := 32#usize }
          hstart7 hend7
          (by simpa [Array.to_slice, Slice.length] using hlen7)
          hindexNorm7 hcopy7 (20 + k) (by change 20 + k < (28#usize).val; rw [hstartNat7]; omega)
      _ = (back6 copied6).val[20 + k]? := by rfl
      _ = base6.val[20 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base6 (Array.to_slice a6) target6 copied6 back6
          { start := 24#usize, «end» := 28#usize }
          hstart6 hend6
          (by simpa [Array.to_slice, Slice.length] using hlen6)
          hindexNorm6 hcopy6 (20 + k) (by change 20 + k < (24#usize).val; rw [hstartNat6]; omega)
      _ = (back5 copied5).val[20 + k]? := by rfl
      _ = a5.val[k]? := by
        have := hslot5 k hk
        simpa using this
  · refine ⟨m6, a6, hread6, hencode6, ?_⟩
    intro k hk
    calc
      out.val[24 + k]? = (back7 copied7).val[24 + k]? := by rw [hfinal]
      _ = base7.val[24 + k]? := by
        exact AspisR1PairForestLaneEncoderTailRangeWriteFrame.range_copy_preserves_prefix_slice
          base7 (Array.to_slice a7) target7 copied7 back7
          { start := 28#usize, «end» := 32#usize }
          hstart7 hend7
          (by simpa [Array.to_slice, Slice.length] using hlen7)
          hindexNorm7 hcopy7 (24 + k) (by change 24 + k < (28#usize).val; rw [hstartNat7]; omega)
      _ = (back6 copied6).val[24 + k]? := by rfl
      _ = a6.val[k]? := by
        have := hslot6 k hk
        simpa using this
  · refine ⟨m7, a7, hread7, hencode7, ?_⟩
    intro k hk
    calc
      out.val[28 + k]? = (back7 copied7).val[28 + k]? := by rw [hfinal]
      _ = a7.val[k]? := by
        have := hslot7 k hk
        simpa using this

#print axioms successful_digest_chunks
end AspisR1PairForestLaneEncoderTailActualDigestChunks
