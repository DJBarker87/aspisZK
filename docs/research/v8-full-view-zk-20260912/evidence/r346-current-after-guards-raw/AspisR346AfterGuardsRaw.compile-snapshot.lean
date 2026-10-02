import Aeneas.Std
import AspisR318BatchPrefixRaw
import AspisR305BatchReverseRaw
import AspisR278PrivateInverseRaw
import AspisR340BatchOutputRaw
import AspisR316SliceLastRaw
import Aeneas.Data.Discriminant

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR249R110Raw AspisR318BatchPrefixRaw AspisR305BatchReverseRaw
open AspisR278PrivateInverseRaw AspisR340BatchOutputRaw
open AspisR316SliceLastRaw

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR346AfterGuardsRaw

/-- [aspis_v8_performance_host::Error]
    Source: '../relation_callback.rs', lines 62:27-62:101 -/
@[discriminant isize]
inductive Error where
| Length : Error
| Canonical : Error
| Sampler : Error
| Shape : Error
| Authentication : Error
| Terminal : Error
| Domain : Error



def selectedAfterGuards (xs ys : Slice U32) :
    Result (core.result.Result (VecU32 × VecU32) AspisR346AfterGuardsRaw.Error) := do
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
        let i3 := Slice.len xs
        let ox ←
          alloc.vec.from_elem
            circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone
            circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO i3
        let i4 := Slice.len xs
        let iter2 ←
          core.iter.traits.iterator.Iterator.rev.trait_default
            (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
            (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize) { start := 1#usize, «end» := i4 }
        let (ix1, ox1) ←
          circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2 iter2 xs
            px2 ix ox
        let (_, index_mut_back) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
            circle_norm.joined_inverse.line_norm.r110_norm.B) ox1 0#usize
        let ox2 := index_mut_back ix1
        let i5 := Slice.len ys
        let oy ←
          alloc.vec.from_elem
            circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone
            circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO i5
        let i6 := Slice.len ys
        let iter3 ←
          core.iter.traits.iterator.Iterator.rev.trait_default
            (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
            (core.ops.range.Range.Insts.DoubleEndedIterator
            core.iter.range.StepUsize) { start := 1#usize, «end» := i6 }
        let (iy1, oy1) ←
          circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3 iter3 ys
            py2 iy oy
        let (_, index_mut_back1) ←
          alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
            circle_norm.joined_inverse.line_norm.r110_norm.B) oy1 0#usize
        let oy2 := index_mut_back1 iy1
        ok (core.result.Result.Ok (ox2, oy2))


#print axioms Error
#print axioms selectedAfterGuards

end AspisR346AfterGuardsRaw
end
