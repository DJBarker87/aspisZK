import Aeneas.Std
import AspisR249R110Raw

open Aeneas.Std Result ControlFlow Error AspisR249R110Raw

noncomputable section
namespace AspisR305BatchReverseRaw

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch]: loop body 2:
    Source: '../r110_norm.rs', lines 66:38-66:107 -/
@[rust_loop_body]
def circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2.body
  (xs : Slice circle_norm.joined_inverse.line_norm.r110_norm.B)
  (px : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (ix : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (ox : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × circle_norm.joined_inverse.line_norm.r110_norm.B ×
    (alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B))
    (circle_norm.joined_inverse.line_norm.r110_norm.B × (alloc.vec.Vec
    circle_norm.joined_inverse.line_norm.r110_norm.B)))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done (ix, ox))
  | some i =>
    let i1 ← lift (Std.Usize.wrapping_sub i 1#usize)
    let b ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        circle_norm.joined_inverse.line_norm.r110_norm.B) px i1
    let b1 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul b ix
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        circle_norm.joined_inverse.line_norm.r110_norm.B) ox i
    let ox1 := index_mut_back b1
    let b2 ← Slice.index_usize xs i
    let ix1 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul ix b2
    ok (cont (iter1, ix1, ox1))

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch]: loop 2:
    Source: '../r110_norm.rs', lines 66:38-66:107 -/
@[rust_loop]
def circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (xs : Slice circle_norm.joined_inverse.line_norm.r110_norm.B)
  (px : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B)
  (ix : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (ox : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (circle_norm.joined_inverse.line_norm.r110_norm.B × (alloc.vec.Vec
    circle_norm.joined_inverse.line_norm.r110_norm.B))
  := do
  loop
    (fun (iter1, ix1, ox1) =>
      circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2.body xs px
      iter1 ix1 ox1)
    (iter, ix, ox)

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch]: loop body 3:
    Source: '../r110_norm.rs', lines 67:38-67:107 -/
@[rust_loop_body]
def circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3.body
  (ys : Slice circle_norm.joined_inverse.line_norm.r110_norm.B)
  (py : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (iy : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (oy : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × circle_norm.joined_inverse.line_norm.r110_norm.B ×
    (alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B))
    (circle_norm.joined_inverse.line_norm.r110_norm.B × (alloc.vec.Vec
    circle_norm.joined_inverse.line_norm.r110_norm.B)))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done (iy, oy))
  | some i =>
    let i1 ← lift (Std.Usize.wrapping_sub i 1#usize)
    let b ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        circle_norm.joined_inverse.line_norm.r110_norm.B) py i1
    let b1 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul b iy
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        circle_norm.joined_inverse.line_norm.r110_norm.B) oy i
    let oy1 := index_mut_back b1
    let b2 ← Slice.index_usize ys i
    let iy1 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul iy b2
    ok (cont (iter1, iy1, oy1))

/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch]: loop 3:
    Source: '../r110_norm.rs', lines 67:38-67:107 -/
@[rust_loop]
def circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (ys : Slice circle_norm.joined_inverse.line_norm.r110_norm.B)
  (py : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B)
  (iy : circle_norm.joined_inverse.line_norm.r110_norm.B)
  (oy : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (circle_norm.joined_inverse.line_norm.r110_norm.B × (alloc.vec.Vec
    circle_norm.joined_inverse.line_norm.r110_norm.B))
  := do
  loop
    (fun (iter1, iy1, oy1) =>
      circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3.body ys py
      iter1 iy1 oy1)
    (iter, iy, oy)

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2.body

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch_loop2

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3.body

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.batch_loop3

end AspisR305BatchReverseRaw
