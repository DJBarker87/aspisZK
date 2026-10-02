/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch]: loop body 0:
    Source: '../r110_norm.rs', lines 63:59-63:114 -/
@[rust_loop_body]
def circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0.body
  (iter : core.slice.iter.Iter
  circle_norm.joined_inverse.line_norm.r110_norm.B)
  (px : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (ControlFlow ((core.slice.iter.Iter
    circle_norm.joined_inverse.line_norm.r110_norm.B) × (alloc.vec.Vec
    circle_norm.joined_inverse.line_norm.r110_norm.B)) (alloc.vec.Vec
    circle_norm.joined_inverse.line_norm.r110_norm.B))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done px)
  | some x =>
    let s := alloc.vec.Vec.deref px
    let o1 ← core.slice.Slice.last s
    let b ← core.option.Option.unwrap o1
    let b1 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul b x
    let px1 ← alloc.vec.Vec.push px b1
    ok (cont (iter1, px1))


/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch]: loop 0:
    Source: '../r110_norm.rs', lines 63:59-63:114 -/
@[rust_loop]
def circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0
  (iter : core.slice.iter.Iter
  circle_norm.joined_inverse.line_norm.r110_norm.B)
  (px : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B)
  := do
  loop
    (fun (iter1, px1) =>
      circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0.body iter1
      px1)
    (iter, px)


/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch]: loop body 1:
    Source: '../r110_norm.rs', lines 64:59-64:114 -/
@[rust_loop_body]
def circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1.body
  (iter : core.slice.iter.Iter
  circle_norm.joined_inverse.line_norm.r110_norm.B)
  (py : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (ControlFlow ((core.slice.iter.Iter
    circle_norm.joined_inverse.line_norm.r110_norm.B) × (alloc.vec.Vec
    circle_norm.joined_inverse.line_norm.r110_norm.B)) (alloc.vec.Vec
    circle_norm.joined_inverse.line_norm.r110_norm.B))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done py)
  | some y =>
    let s := alloc.vec.Vec.deref py
    let o1 ← core.slice.Slice.last s
    let b ← core.option.Option.unwrap o1
    let b1 ← circle_norm.joined_inverse.line_norm.r110_norm.B.mul b y
    let py1 ← alloc.vec.Vec.push py b1
    ok (cont (iter1, py1))


/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch]: loop 1:
    Source: '../r110_norm.rs', lines 64:59-64:114 -/
@[rust_loop]
def circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1
  (iter : core.slice.iter.Iter
  circle_norm.joined_inverse.line_norm.r110_norm.B)
  (py : alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B) :
  Result (alloc.vec.Vec circle_norm.joined_inverse.line_norm.r110_norm.B)
  := do
  loop
    (fun (iter1, py1) =>
      circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1.body iter1
      py1)
    (iter, py)
