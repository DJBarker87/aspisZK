import CuSavingsPrefix

/-! Prefix invariance through the actual checked offset-arithmetic sequences.
Every continuation is arbitrary: later decoder success is not assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.CuSavingsDotsReads
open Aeneas Aeneas.Std Result
open CuSavingsPrefix

theorem range_index (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (r : core.ops.range.Range Usize) (hr : r.end.val ≤ 608) :
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        (prefixArray bytes h).to_slice r =
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes r := by
  have hp : (prefixArray bytes h).to_slice.length = 608 := by
    simpa only [Array.to_slice,Slice.length,show (608#usize).val = 608 by scalar_tac]
      using (prefixArray bytes h).property
  simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice.index]
  by_cases ho : r.start.val ≤ r.end.val
  · rw [if_pos ⟨ho,by simpa only [hp] using hr⟩,
      if_pos ⟨ho,show r.end.val ≤ bytes.length from by change r.end.val ≤ bytes.val.length;omega⟩]
    apply congrArg Result.ok
    apply Subtype.ext
    exact range_eq bytes h r.start.val r.end.val hr
  · rw [if_neg (by exact fun hc => ho hc.1),if_neg (by exact fun hc => ho hc.1)]

theorem add_val (x y z : Usize) (h : (x+y : Result Usize) = .ok z) :
    z.val = x.val+y.val := by
  have hs := UScalar.add_equiv x y
  rw [h] at hs
  exact hs.2.1

theorem mul_val (x y z : Usize) (h : (x*y : Result Usize) = .ok z) :
    z.val = x.val*y.val := by
  have hs := UScalar.mul_equiv x y
  change UScalar.mul x y = .ok z at h
  rw [h] at hs
  exact hs.2.1

theorem base_cont {A : Type} (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (slot term : Usize) (hs : slot.val < 4) (ht : term.val < 26)
    (k : Slice U8 → Result A) :
    (do let i ← slot * 120#usize
        let i1 ← term * 4#usize
        let i2 ← i + i1
        let i3 ← i + i1
        let i4 ← i3 + 4#usize
        let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          (prefixArray bytes h).to_slice {start := i2,«end» := i4}
        k s) =
    (do let i ← slot * 120#usize
        let i1 ← term * 4#usize
        let i2 ← i + i1
        let i3 ← i + i1
        let i4 ← i3 + 4#usize
        let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          bytes {start := i2,«end» := i4}
        k s) := by
  apply bind_eq_iff.mpr;intro i hi
  apply bind_eq_iff.mpr;intro i1 hi1
  apply bind_eq_iff.mpr;intro i2 hi2
  apply bind_eq_iff.mpr;intro i3 hi3
  apply bind_eq_iff.mpr;intro i4 hi4
  have hv := mul_val _ _ _ hi
  have hv1 := mul_val _ _ _ hi1
  have hv3 := add_val _ _ _ hi3
  have hv4 := add_val _ _ _ hi4
  have h120 : (120#usize).val = 120 := by scalar_tac
  have h4 : (4#usize).val = 4 := by scalar_tac
  rw [range_index bytes h _ (by dsimp only;rw [hv4,hv3,hv,hv1,h120,h4];omega)]

theorem middle_cont {A : Type} (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (slot : Usize) (hs : slot.val < 4) (k : Slice U8 → Result A) :
    (do let i ← slot * 120#usize
        let i1 ← i + 104#usize
        let i2 ← i + 120#usize
        let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          (prefixArray bytes h).to_slice {start := i1,«end» := i2}
        k s) =
    (do let i ← slot * 120#usize
        let i1 ← i + 104#usize
        let i2 ← i + 120#usize
        let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          bytes {start := i1,«end» := i2}
        k s) := by
  apply bind_eq_iff.mpr;intro i hi
  apply bind_eq_iff.mpr;intro i1 hi1
  apply bind_eq_iff.mpr;intro i2 hi2
  have hv := mul_val _ _ _ hi
  have hv2 := add_val _ _ _ hi2
  have h120 : (120#usize).val = 120 := by scalar_tac
  rw [range_index bytes h _ (by dsimp only;rw [hv2,hv,h120];omega)]

theorem tail_cont {A C : Type} (bytes : Slice U8) (h : 608 ≤ bytes.val.length)
    (slot term : Usize) (hs : slot.val < 4) (ht : term.val < 2)
    (before : Usize → Result C) (k : C → Slice U8 → Result A) :
    (do let i ← slot * 32#usize
        let i1 ← 480#usize + i
        let i2 ← term * 16#usize
        let offset ← i1 + i2
        let i3 ← term + 26#usize
        let value ← before i3
        let i4 ← offset + 16#usize
        let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          (prefixArray bytes h).to_slice {start := offset,«end» := i4}
        k value s) =
    (do let i ← slot * 32#usize
        let i1 ← 480#usize + i
        let i2 ← term * 16#usize
        let offset ← i1 + i2
        let i3 ← term + 26#usize
        let value ← before i3
        let i4 ← offset + 16#usize
        let s ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
          bytes {start := offset,«end» := i4}
        k value s) := by
  apply bind_eq_iff.mpr;intro i hi
  apply bind_eq_iff.mpr;intro i1 hi1
  apply bind_eq_iff.mpr;intro i2 hi2
  apply bind_eq_iff.mpr;intro offset hoff
  apply bind_eq_iff.mpr;intro i3 hi3
  apply bind_eq_iff.mpr;intro value hvalue
  apply bind_eq_iff.mpr;intro i4 hi4
  have hv := mul_val _ _ _ hi
  have hv1 := add_val _ _ _ hi1
  have hv2 := mul_val _ _ _ hi2
  have hvo := add_val _ _ _ hoff
  have hv4 := add_val _ _ _ hi4
  have h32 : (32#usize).val = 32 := by scalar_tac
  have h16 : (16#usize).val = 16 := by scalar_tac
  have h480 : (480#usize).val = 480 := by scalar_tac
  rw [range_index bytes h _ (by dsimp only;rw [hv4,hvo,hv1,hv2,hv,h32,h16,h480];omega)]

#print axioms range_index
#print axioms base_cont
#print axioms middle_cont
#print axioms tail_cont
end AspisR1.CuSavingsDotsReads
