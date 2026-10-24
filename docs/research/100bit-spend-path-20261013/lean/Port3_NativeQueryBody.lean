import Port3_NativePendingPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeQueryBody
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
structure Ops where
  op0 : ∀ {T : Type} {F : Type} (N : Std.Usize) (opsfunctionFnMutFTupleUsizeTInst :
      core.ops.function.FnMut F Std.Usize T), F → Result (Array T N)
  op1 : aspis_core.field.QM31 → Result aspis_core.field.wide_exact.WideExact
  op2 : aspis_core.field.wide_exact.WideExact →
        aspis_core.field.wide_exact.WideExact → Result
        aspis_core.field.wide_exact.WideExact
  op3 : aspis_core.field.wide_exact.WideExact → aspis_core.field.QM31 → Result
        aspis_core.field.wide_exact.WideExact
  op4 : Result aspis_core.field.M31
  op5 : Result aspis_core.field.M31
  op6 : aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op7 : aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op8 : aspis_core.field.M31 → Result aspis_core.field.M31
  op9 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result
        aspis_core.field.QM31
  op10 : aspis_core.field.M31 → Result aspis_core.field.wide_exact.WideExact
  op11 : (Slice Std.U8) → Std.Usize → Result (Slice Std.U8)
  op12 : (Slice aspis_core.field.QM31) → Std.Usize → Result aspis_core.field.QM31
  op13 : (Array aspis_core.field.M31 256#usize) → Std.Usize → Result
        aspis_core.field.M31
  op14 : verifier.BatchedWeights → Std.Usize → aspis_core.field.QM31 →
        aspis_core.field.M31 → Result verifier.BatchedWeights
  op15 : Std.U16 → Std.Usize → aspis_core.field.wide_exact.WideExact → Result
        Unit
  op16 : aspis_core.field.wide_exact.WideExact → (Array
        aspis_core.field.wide_exact.WideExact 4#usize) → (Array
        aspis_core.field.M31 5#usize) → Result
        aspis_core.field.wide_exact.WideExact
  op17 : aspis_core.field.wide_exact.WideExact → (Array
        aspis_core.field.wide_exact.WideExact 4#usize) → (Array
        aspis_core.field.M31 5#usize) → Result
        aspis_core.field.wide_exact.WideExact
  op18 : verifier.QueryGeometry → Std.Usize → Result (Array aspis_core.field.M31
        5#usize)
  op19 : (Option (verifier.Phase → Result Unit)) → verifier.Phase → Result Unit
  op20 : (Slice Std.U8) → (Array aspis_core.field.wide_exact.WideExact 29#usize) →
        Result (Array aspis_core.field.wide_exact.WideExact 4#usize)
  op21 : (Slice Std.U8) → Std.Usize → Result aspis_core.field.wide_exact.WideExact
  widePartialEq : core.cmp.PartialEq aspis_core.field.wide_exact.WideExact aspis_core.field.wide_exact.WideExact

def verifier.accumulate_batched_with_node_loop0_loop0.body (ops : Ops)
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
    let m1 ← ops.op7 m node
    let i ← lift (Std.Usize.wrapping_add n j)
    let basis1 ← Array.update basis i m1
    ok (cont (iter1, basis1))

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 280:19-280:65 -/
@[rust_loop]
def verifier.accumulate_batched_with_node_loop0_loop0 (ops : Ops)
  (iter : core.ops.range.Range Std.Usize) (node : aspis_core.field.M31)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (Array aspis_core.field.M31 256#usize)
  := do
  loop
    (fun (iter1, basis1) =>
      (verifier.accumulate_batched_with_node_loop0_loop0.body ops) node n iter1
      basis1)
    (iter, basis)

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 280:4-280:115 -/
@[rust_loop_body]
def verifier.accumulate_batched_with_node_loop0.body (ops : Ops)
  (m : aspis_core.field.M31) (width : Std.Usize) (node : aspis_core.field.M31)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (ControlFlow (aspis_core.field.M31 × (Array aspis_core.field.M31
    256#usize) × Std.Usize) (Array aspis_core.field.M31 256#usize))
  := do
  if n < width
  then
    let basis1 ←
      (verifier.accumulate_batched_with_node_loop0_loop0 ops)
        { start := 0#usize, «end» := n } node basis n
    let m1 ← ops.op7 node node
    let m2 ← ops.op8 m1
    let node1 ← ops.op6 m2 m
    let n1 ← lift (Std.Usize.wrapping_mul n 2#usize)
    ok (cont (node1, basis1, n1))
  else ok (done basis)

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 280:4-280:115 -/
@[rust_loop]
def verifier.accumulate_batched_with_node_loop0 (ops : Ops)
  (m : aspis_core.field.M31) (node : aspis_core.field.M31) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) (n : Std.Usize) :
  Result (Array aspis_core.field.M31 256#usize)
  := do
  loop
    (fun (node1, basis1, n1) =>
      (verifier.accumulate_batched_with_node_loop0.body ops) m width node1 basis1 n1)
    (node, basis, n)

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop body 2:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 281:4-286:5 -/
@[rust_loop_body]
def verifier.accumulate_batched_with_node_loop1.body (ops : Ops)
  (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
  (i : Std.Usize) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize)
  (iter : core.ops.range.Range Std.Usize) (weights : verifier.BatchedWeights) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) ×
    verifier.BatchedWeights) verifier.BatchedWeights)
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done weights)
  | some j =>
    let m ← ops.op13 basis j
    let weights1 ← ops.op14 weights j q m
    let i1 ← lift (Std.Usize.wrapping_mul i width)
    let i2 ← lift (Std.Usize.wrapping_add i1 j)
    let s := alloc.vec.Vec.deref v
    let q1 ← ops.op12 s j
    let we ← ops.op1 q1
    ops.op15 12#u16 i2 we
    let i3 ← lift (Std.Usize.wrapping_mul i width)
    let i4 ← lift (Std.Usize.wrapping_add i3 j)
    let we1 ←
      ops.op10
        m
    ops.op15 13#u16 i4 we1
    ok (cont (iter1, weights1))

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]: loop 2:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 281:4-286:5 -/
@[rust_loop]
def verifier.accumulate_batched_with_node_loop1 (ops : Ops)
  (iter : core.ops.range.Range Std.Usize)
  (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
  (i : Std.Usize) (weights : verifier.BatchedWeights) (width : Std.Usize)
  (basis : Array aspis_core.field.M31 256#usize) :
  Result verifier.BatchedWeights
  := do
  loop
    (fun (iter1, weights1) => (verifier.accumulate_batched_with_node_loop1.body ops)
      v q i width basis iter1 weights1)
    (iter, weights)

/-- [aspis_r1_cost_probe::verifier::accumulate_batched_with_node]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 277:0-290:1 -/
def verifier.accumulate_batched_with_node (ops : Ops)
  (p : verifier.Prepared) (a : verifier.Accumulator)
  (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
  (weights : verifier.BatchedWeights) :
  Result (verifier.Accumulator × verifier.BatchedWeights)
  := do
  let width := alloc.vec.Vec.len a.weights
  let m ← ops.op4
  let basis := Array.repeat 256#usize m
  let m1 ← ops.op5
  let basis1 ← Array.update basis 0#usize m1
  let basis2 ←
    (verifier.accumulate_batched_with_node_loop0 ops) m1 node width basis1 1#usize
  let weights1 ←
    (verifier.accumulate_batched_with_node_loop1 ops)
      { start := 0#usize, «end» := width } a.weights a.power a.next weights
      width basis2
  let i ← lift (Std.Usize.wrapping_add weights1.terms 1#usize)
  let we ← ops.op3 value a.power
  let we1 ← ops.op2 a.rhs we
  ops.op15 11#u16 a.next we1
  let q ← ops.op9 a.power p.rho
  let i1 ← lift (Std.Usize.wrapping_add a.next 1#usize)
  ok ({ a with rhs := we1, power := q, next := i1 },
    { weights1 with terms := i })

/-- [aspis_r1_cost_probe::verifier::candidate::query_values::{impl core::ops::function::FnMut<(usize,), aspis_core::field::wide_exact::WideExact> for aspis_r1_cost_probe::verifier::candidate::query_values::closure<'_0>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 224:38-224:64 -/
def verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut (ops : Ops)
  (c : verifier.candidate.query_values.closure) (tupled_args : Std.Usize) :
  Result (aspis_core.field.wide_exact.WideExact ×
    verifier.candidate.query_values.closure)
  := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) c { start := 672#usize, «end» := 800#usize }
  let we ← ops.op21 s tupled_args
  ok (we, c)

/-- [aspis_r1_cost_probe::verifier::candidate::query_values::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::wide_exact::WideExact> for aspis_r1_cost_probe::verifier::candidate::query_values::closure<'_0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 224:38-224:64 -/
def verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once (ops : Ops)
  (c : verifier.candidate.query_values.closure) (i : Std.Usize) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let (we, _) ←
    (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut ops)
      c i
  ok we

/-- Trait implementation: [aspis_r1_cost_probe::verifier::candidate::query_values::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::wide_exact::WideExact> for aspis_r1_cost_probe::verifier::candidate::query_values::closure<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 224:38-224:64 -/
@[reducible]
def verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact (ops : Ops)
  : core.ops.function.FnOnce verifier.candidate.query_values.closure Std.Usize
  aspis_core.field.wide_exact.WideExact := {
  call_once :=
    (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once ops)
}

/-- Trait implementation: [aspis_r1_cost_probe::verifier::candidate::query_values::{impl core::ops::function::FnMut<(usize,), aspis_core::field::wide_exact::WideExact> for aspis_r1_cost_probe::verifier::candidate::query_values::closure<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 224:38-224:64 -/
@[reducible]
def verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact (ops : Ops)
  : core.ops.function.FnMut verifier.candidate.query_values.closure Std.Usize
  aspis_core.field.wide_exact.WideExact := {
  FnOnceInst :=
    (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact ops)
  call_mut :=
    (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut ops)
}

/-- [aspis_r1_cost_probe::verifier::candidate::query_values]:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 212:0-235:1 -/
def verifier.candidate.query_values (ops : Ops)
  (proof : Slice Std.U8) (p : verifier.Prepared) (a : verifier.Accumulator)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights) :
  Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
    verifier.Error)
  := do
  let i ← Array.index_usize p.queries a.next
  let u ← lift (UScalar.cast .Usize i)
  let q ← ops.op11 proof a.next
  let dots ← ops.op20 q g
  let i1 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let we ← Array.index_usize dots 0#usize
  ops.op15 9#u16 i1 we
  let i2 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let i3 ← lift (Std.Usize.wrapping_add i2 1#usize)
  let we1 ← Array.index_usize dots 1#usize
  ops.op15 9#u16 i3 we1
  let i4 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let i5 ← lift (Std.Usize.wrapping_add i4 2#usize)
  let we2 ← Array.index_usize dots 2#usize
  ops.op15 9#u16 i5 we2
  let i6 ← lift (Std.Usize.wrapping_mul 4#usize a.next)
  let i7 ← lift (Std.Usize.wrapping_add i6 3#usize)
  let we3 ← Array.index_usize dots 3#usize
  ops.op15 9#u16 i7 we3
  let inverse ← ops.op18 geometry a.next
  let we4 ← Array.index_usize p.alpha 0#usize
  let folded ← ops.op17 we4 dots inverse
  let i8 ← lift (Std.Usize.wrapping_mul 2#usize a.next)
  ops.op15 10#u16 i8 folded
  let values ←
    ops.op0 4#usize
      (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact ops)
      q
  let i9 ← u % 4#usize
  let we5 ← Array.index_usize values i9
  let b ←
    core.cmp.PartialEq.ne.trait_default
      ops.widePartialEq
      folded we5
  if b
  then ok (core.result.Result.Err verifier.Error.Query)
  else
    let we6 ← Array.index_usize p.alpha 1#usize
    let folded1 ← ops.op16 we6 values inverse
    let i10 ← lift (Std.Usize.wrapping_mul 2#usize a.next)
    let i11 ← lift (Std.Usize.wrapping_add i10 1#usize)
    ops.op15 10#u16 i11 folded1
    let i12 ← lift (Std.Usize.wrapping_sub a.next geometry.start)
    let z ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) geometry.line_z i12
    let m ← ops.op7 z z
    let m1 ← ops.op8 m
    let m2 ← ops.op5
    let node ← ops.op6 m1 m2
    let (a1, pending1) ←
      (verifier.accumulate_batched_with_node ops) p a node folded1 pending
    ops.op19 obs (verifier.Phase.Query a.next)
    ok (core.result.Result.Ok (a1, pending1))

/-- [aspis_r1_cost_probe::verifier::candidate::query_loop]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 242:8-249:13 -/
@[rust_loop_body]
def verifier.candidate.query_loop_loop.body (ops : Ops)
  (proof : Slice Std.U8) (p : verifier.Prepared)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (end1 : Std.Usize)
  (state : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
  verifier.Error) :
  Result (ControlFlow (core.result.Result (verifier.Accumulator ×
    verifier.BatchedWeights) verifier.Error) (core.result.Result
    (verifier.Accumulator × verifier.BatchedWeights) verifier.Error))
  := do
  match state with
  | core.result.Result.Ok p1 =>
    let (a, pending) := p1
    if a.next >= end1
    then ok (done state)
    else
      let state1 ←
        (verifier.candidate.query_values ops) proof p a g obs geometry pending
      ok (cont state1)
  | core.result.Result.Err _ => ok (done state)

/-- [aspis_r1_cost_probe::verifier::candidate::query_loop]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 242:8-249:13 -/
@[rust_loop]
def verifier.candidate.query_loop_loop (ops : Ops)
  (state : core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
  verifier.Error) (proof : Slice Std.U8) (p : verifier.Prepared)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (end1 : Std.Usize) :
  Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
    verifier.Error)
  := do
  loop
    (fun state1 => (verifier.candidate.query_loop_loop.body ops) proof p g obs
      geometry end1 state1)
    state

/-- [aspis_r1_cost_probe::verifier::candidate::query_loop]:
    Source: 'crates/aspis-r1-cost-probe/src/candidate.rs', lines 239:0-252:1 -/
@[reducible]
def verifier.candidate.query_loop (ops : Ops)
  (proof : Slice Std.U8) (p : verifier.Prepared) (a : verifier.Accumulator)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  (obs : Option (verifier.Phase → Result Unit))
  (geometry : verifier.QueryGeometry) (pending : verifier.BatchedWeights)
  (end1 : Std.Usize) :
  Result (core.result.Result (verifier.Accumulator × verifier.BatchedWeights)
    verifier.Error)
  := do
  (verifier.candidate.query_loop_loop ops) (core.result.Result.Ok (a, pending)) proof
    p g obs geometry end1


#print axioms verifier.accumulate_batched_with_node_loop0_loop0.body
#print axioms verifier.accumulate_batched_with_node_loop0_loop0
#print axioms verifier.accumulate_batched_with_node_loop0.body
#print axioms verifier.accumulate_batched_with_node_loop0
#print axioms verifier.accumulate_batched_with_node_loop1.body
#print axioms verifier.accumulate_batched_with_node_loop1
#print axioms verifier.accumulate_batched_with_node
#print axioms verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut
#print axioms verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact.call_once
#print axioms verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeWideExact
#print axioms verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
#print axioms verifier.candidate.query_values
#print axioms verifier.candidate.query_loop_loop.body
#print axioms verifier.candidate.query_loop_loop
#print axioms verifier.candidate.query_loop
end AspisR1.Port3_NativeQueryBody
end
