namespace NEV_AccumulateRaw

/-- [neg_isolated::basis_at]:
    Source: 'src/lib.rs', lines 66:0-66:61 -/
def basis_at
  (basis : Array aspis_core.field.M31 256#usize) (index : Std.Usize) :
  Result aspis_core.field.M31
  := do
  Array.index_usize basis index

/-- [neg_isolated::accumulated_weight_at]:
    Source: 'src/lib.rs', lines 67:0-67:70 -/
def accumulated_weight_at
  (weights : Slice aspis_core.field.QM31) (index : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  Slice.index_usize weights index

/-- [neg_isolated::accumulate_batched_with_node]: loop body 1:
    Source: 'src/lib.rs', lines 71:19-71:65 -/
@[rust_loop_body]
def accumulate_batched_with_node_loop0_loop0.body
  (node : aspis_core.field.M31) (n : Std.Usize)
  (iter : core.ops.range.Range Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.M31 256#usize)) (Array aspis_core.field.M31 256#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done basis)
  | some j =>
    let m ← Array.index_usize basis j
    let m1 ← aspis_core.field.M31.mul m node
    let i ← n + j
    let basis1 ← Array.update basis i m1
    ok (cont (iter1, basis1))

/-- [neg_isolated::accumulate_batched_with_node]: loop 1:
    Source: 'src/lib.rs', lines 71:19-71:65 -/
@[rust_loop]
def accumulate_batched_with_node_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (node : aspis_core.field.M31)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (Array aspis_core.field.M31 256#usize)
  := do
  loop
    (fun (iter1, basis1) => accumulate_batched_with_node_loop0_loop0.body node
      n iter1 basis1)
    (iter, basis)

/-- [neg_isolated::accumulate_batched_with_node]: loop body 0:
    Source: 'src/lib.rs', lines 71:4-71:115 -/
@[rust_loop_body]
def accumulate_batched_with_node_loop0.body
  (m : aspis_core.field.M31) (width : Std.Usize) (node : aspis_core.field.M31)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (ControlFlow (aspis_core.field.M31 × (Array aspis_core.field.M31
    256#usize) × Std.Usize) (Array aspis_core.field.M31 256#usize))
  := do
  if n < width
  then
    let basis1 ←
      accumulate_batched_with_node_loop0_loop0
        { start := 0#usize, «end» := n } node basis n
    let m1 ← aspis_core.field.M31.mul node node
    let m2 ← aspis_core.field.M31.double m1
    let node1 ← aspis_core.field.M31.sub m2 m
    let n1 ← n * 2#usize
    ok (cont (node1, basis1, n1))
  else ok (done basis)

/-- [neg_isolated::accumulate_batched_with_node]: loop 0:
    Source: 'src/lib.rs', lines 71:4-71:115 -/
@[rust_loop]
def accumulate_batched_with_node_loop0
  (m : aspis_core.field.M31) (node : aspis_core.field.M31) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (Array aspis_core.field.M31 256#usize)
  := do
  loop
    (fun (node1, basis1, n1) => accumulate_batched_with_node_loop0.body m width
      node1 basis1 n1)
    (node, basis, n)

/-- [neg_isolated::accumulate_batched_with_node]: loop body 2:
    Source: 'src/lib.rs', lines 72:4-77:5 -/
@[rust_loop_body]
def accumulate_batched_with_node_loop1.body
  (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
  (i : Std.Usize) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize)
  (iter : core.ops.range.Range Std.Usize) (weights : BatchedWeights) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × BatchedWeights)
    BatchedWeights)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done weights)
  | some j =>
    let m ← basis_at basis j
    let weights1 ← BatchedWeights.push weights j q m
    let i1 ← i * width
    let i2 ← i1 + j
    let s := alloc.vec.Vec.deref v
    let q1 ← accumulated_weight_at s j
    let we ← aspis_core.field.wide_exact.WideExact.from_qm31 q1
    trace.value 12#u16 i2 we
    let i3 ← i1 + j
    let we1 ←
      aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
        m
    trace.value 13#u16 i3 we1
    ok (cont (iter1, weights1))

/-- [neg_isolated::accumulate_batched_with_node]: loop 2:
    Source: 'src/lib.rs', lines 72:4-77:5 -/
@[rust_loop]
def accumulate_batched_with_node_loop1
  (iter : core.ops.range.Range Std.Usize)
  (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
  (i : Std.Usize) (weights : BatchedWeights) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) :
  Result BatchedWeights
  := do
  loop
    (fun (iter1, weights1) => accumulate_batched_with_node_loop1.body v q i
      width basis iter1 weights1)
    (iter, weights)

/-- [neg_isolated::accumulate_batched_with_node]:
    Source: 'src/lib.rs', lines 68:0-81:1 -/
def accumulate_batched_with_node
  (p : Prepared) (a : Accumulator) (node : aspis_core.field.M31)
  (value : aspis_core.field.wide_exact.WideExact) (weights : BatchedWeights) :
  Result (Accumulator × BatchedWeights)
  := do
  let width := alloc.vec.Vec.len a.weights
  let m ← aspis_core.field.M31.ZERO
  let basis := Array.repeat 256#usize m
  let m1 ← aspis_core.field.M31.ONE
  let basis1 ← Array.update basis 0#usize m1
  let basis2 ←
    accumulate_batched_with_node_loop0 m1 node width basis1 1#usize
  let weights1 ←
    accumulate_batched_with_node_loop1 { start := 0#usize, «end» := width }
      a.weights a.power a.next weights width basis2
  let i ← weights1.terms + 1#usize
  let we ← aspis_core.field.wide_exact.WideExact.mul_qm31 value a.power
  let we1 ← aspis_core.field.wide_exact.WideExact.add a.rhs we
  trace.value 11#u16 a.next we1
  let q ← aspis_core.field.QM31.mul a.power p.rho
  let i1 ← a.next + 1#usize
  ok ({ a with rhs := we1, power := q, next := i1 },
    { weights1 with terms := i })

end NEV_AccumulateRaw
