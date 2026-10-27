import RPu_FJa_SliceBounds
set_option autoImplicit false
namespace AspisR1.FJa_SlicesValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
theorem high (point : Array NQ 10#usize) (s : Slice NQ)
    (run : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice NQ)) point ⟨6#usize⟩=ok s) :
    s.val=point.val.take 6 ∧ s.val.length=6 := by
  unfold core.array.Array.index core.ops.index.IndexSlice
    core.slice.index.Slice.index core.slice.index.SliceIndexRangeToUsizeSlice
    core.slice.index.SliceIndexRangeToUsizeSlice.index at run
  simp only [Array.to_slice] at run
  split at run
  · have same := Result.ok.inj run
    subst s
    constructor
    · rfl
    · change (point.val.take 6).length=6
      rw [List.length_take,point.property]
      decide
  · cases run
theorem low (point : Array NQ 10#usize) (s : Slice NQ)
    (run : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice NQ)) point ⟨6#usize⟩=ok s) :
    s.val=point.val.drop 6 ∧ s.val.length=4 := by
  unfold core.array.Array.index core.ops.index.IndexSlice
    core.slice.index.Slice.index core.slice.index.SliceIndexRangeFromUsizeSlice
    core.slice.index.SliceIndexRangeFromUsizeSlice.index at run
  simp only [Array.to_slice] at run
  split at run
  · have same := Result.ok.inj run
    subst s
    constructor
    · rfl
    · simp only [Slice.drop,List.length_drop,point.property]; decide
  · cases run
#print axioms high
#print axioms low
end AspisR1.FJa_SlicesValue
