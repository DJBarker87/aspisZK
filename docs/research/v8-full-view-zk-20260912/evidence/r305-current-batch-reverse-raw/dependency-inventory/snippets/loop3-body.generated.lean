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

