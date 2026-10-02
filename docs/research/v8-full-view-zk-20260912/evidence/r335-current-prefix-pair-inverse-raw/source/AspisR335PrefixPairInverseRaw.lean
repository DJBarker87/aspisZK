import Aeneas.Std
import AspisR318BatchPrefixRaw
import AspisR278PrivateInverseRaw
open Aeneas Aeneas.Std Result ControlFlow Error AspisR249R110Raw AspisR316SliceLastRaw AspisR318BatchPrefixRaw AspisR278PrivateInverseRaw

noncomputable section
namespace AspisR335PrefixPairInverseRaw

def selectedPrefix1 (ys : Slice U32) : Result (alloc.vec.Vec U32) := do
        let i2 := Slice.len ys
        let py :=
          alloc.vec.Vec.with_capacity
            circle_norm.joined_inverse.line_norm.r110_norm.B i2
        let b4 ← Slice.index_usize ys 0#usize
        let py1 ← alloc.vec.Vec.push py b4
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeFromUsizeSlice
            circle_norm.joined_inverse.line_norm.r110_norm.B) ys
            { start := 1#usize }
        let iter1 ←
          SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
            s1
        let py2 ←
          circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1 iter1 py1
        .ok py2

def selectedPairInverse (px2 py2 : alloc.vec.Vec U32) : Result (U32 × U32) := do
        let s2 := alloc.vec.Vec.deref px2
        let o ← core.slice.Slice.last s2
        let p ← core.option.Option.unwrap o
        let s3 := alloc.vec.Vec.deref py2
        let o1 ← core.slice.Slice.last s3
        let q ← core.option.Option.unwrap o1
        let b5 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul p q
        let total ← circle_norm.joined_inverse.line_norm.r110_norm.B.inv b5
        let ix ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul total q
        let iy ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul total p
        .ok (ix, iy)

#print axioms selectedPrefix1
#print axioms selectedPairInverse

end AspisR335PrefixPairInverseRaw
end
