import FIx_ReconstructSlice
set_option autoImplicit false
namespace AspisR1.FIx_ReconstructSlice
open Aeneas Aeneas.Std Result FIq_Native
#print Aeneas.Std.core.slice.index.Slice.index
#print Aeneas.Std.core.slice.index.SliceIndexRangeToUsizeSlice.index

theorem value (view : Array NQ 16#usize) (out : Slice NQ)
    (success : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice NQ)) view ⟨9#usize⟩=ok out) :
    out.val=view.val.take 9 := by
  simp only [core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index] at success
  exact congrArg Subtype.val (Result.ok.inj success).symm
#print axioms value
end AspisR1.FIx_ReconstructSlice
