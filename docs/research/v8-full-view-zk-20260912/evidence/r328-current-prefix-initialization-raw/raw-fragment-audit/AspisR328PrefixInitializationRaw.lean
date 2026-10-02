import Aeneas.Std
import AspisR318BatchPrefixRaw
open Aeneas Aeneas.Std Result ControlFlow Error AspisR249R110Raw AspisR316SliceLastRaw AspisR318BatchPrefixRaw

noncomputable section
namespace AspisR328PrefixInitializationRaw

def selectedPrefix0 (xs : Slice U32) : Result (alloc.vec.Vec U32) := do
        let i1 := Slice.len xs
        let px :=
          alloc.vec.Vec.with_capacity
            circle_norm.joined_inverse.line_norm.r110_norm.B i1
        let b3 ← Slice.index_usize xs 0#usize
        let px1 ← alloc.vec.Vec.push px b3
        let s ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeFromUsizeSlice
            circle_norm.joined_inverse.line_norm.r110_norm.B) xs
            { start := 1#usize }
        let iter ←
          SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
            s
        let px2 ←
          circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0 iter px1
        .ok px2

#print axioms selectedPrefix0

end AspisR328PrefixInitializationRaw
end
