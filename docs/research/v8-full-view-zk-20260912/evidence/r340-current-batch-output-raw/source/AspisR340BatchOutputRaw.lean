import Aeneas.Std
import AspisR305BatchReverseRaw
import AspisR278PrivateInverseRaw

open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR249R110Raw AspisR305BatchReverseRaw AspisR278PrivateInverseRaw

set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR340BatchOutputRaw

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{impl core::clone::Clone for aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}::clone]:
    Source: '../r110_norm.rs', lines 5:9-5:14
    Visibility: public -/
def circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone.clone
  (self : circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result circle_norm.joined_inverse.line_norm.r110_norm.B
  := do
  ok self

/-- Trait implementation: [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::{impl core::clone::Clone for aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::B}]
    Source: '../r110_norm.rs', lines 5:9-5:14 -/
@[reducible]
def circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone :
  core.clone.Clone circle_norm.joined_inverse.line_norm.r110_norm.B := {
  clone :=
    circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone.clone
}


abbrev VecU32 := alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B
abbrev ResultVecU32 := Result VecU32

def selectedOutput0 (xs : Slice U32) (px2 : VecU32) (ix : U32) : ResultVecU32 := do
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
        ok ox2

def selectedOutput1 (ys : Slice U32) (py2 : VecU32) (iy : U32) : ResultVecU32 := do
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
        ok oy2

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone.clone
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.Insts.CoreCloneClone
#print axioms selectedOutput0
#print axioms selectedOutput1

end AspisR340BatchOutputRaw
end
