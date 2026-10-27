import FJa_SliceShape
import FIw_ArrayValue
set_option autoImplicit false
namespace AspisR1.FJa_SliceBounds
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
/-- Native slice indexing retains only cells of its actual point. -/
theorem high (point : Array NQ 10#usize) (s : Slice NQ)
    (hp : FIw_ArrayValue.canonical point)
    (run : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice NQ)) point ⟨6#usize⟩=ok s) :
    ∀ x∈s.val,Canon x := by
  unfold core.array.Array.index core.ops.index.IndexSlice
    core.slice.index.Slice.index core.slice.index.SliceIndexRangeToUsizeSlice
    core.slice.index.SliceIndexRangeToUsizeSlice.index at run
  simp only [Array.to_slice] at run
  split at run
  · have same := Result.ok.inj run
    subst s
    intro x hx
    exact hp x (List.mem_of_mem_take hx)
  · cases run
/-- The low four coordinates come from the SAME suffix of the reader point. -/
theorem low (point : Array NQ 10#usize) (s : Slice NQ)
    (hp : FIw_ArrayValue.canonical point)
    (run : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeFromUsizeSlice NQ)) point ⟨6#usize⟩=ok s) :
    ∀ x∈s.val,Canon x := by
  unfold core.array.Array.index core.ops.index.IndexSlice
    core.slice.index.Slice.index core.slice.index.SliceIndexRangeFromUsizeSlice
    core.slice.index.SliceIndexRangeFromUsizeSlice.index at run
  simp only [Array.to_slice] at run
  split at run
  · have same := Result.ok.inj run
    subst s
    intro x hx
    exact hp x (List.mem_of_mem_drop hx)
  · cases run
#print axioms high
#print axioms low
end AspisR1.FJa_SliceBounds
