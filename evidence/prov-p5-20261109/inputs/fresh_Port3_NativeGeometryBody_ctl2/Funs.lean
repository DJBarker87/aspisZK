import Port3_NativePendingPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativeGeometryBody
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
abbrev aspis_core.r0.domain.FibreIndex := Usize
variable {CoreError : Type}
structure Ops (CoreError : Type) where
  op0 : ∀ {T : Type} {F : Type} (N : Std.Usize) (opsfunctionFnMutFTupleUsizeTInst :
      core.ops.function.FnMut F Std.Usize T), F → Result (Array T N)
  op1 : ∀ {Self : Type} {B : Type} {F : Type} {Clause0_Item : Type} (IteratorInst :
      core.iter.traits.iterator.Iterator Self Clause0_Item)
      (opsfunctionFnMutFTupleClause0_ItemBInst : core.ops.function.FnMut F
      Clause0_Item B), Self → F → Result (core.iter.adapters.map.Map Self F)
  op2 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
      core.ops.function.FnOnce O E F), (core.result.Result T E) → O → Result (core.result.Result T F)
  op3 : ∀ {T : Type} {F : Type} (opsfunctionFnMutFTupleSharedATBoolInst :
      core.ops.function.FnMut F T Bool), (core.slice.iter.Iter T) → F → Result (Bool × (core.slice.iter.Iter T))
  op4 : ∀ {T : Type} (A : Type), (alloc.vec.Vec T) → Result Bool
  op5 : aspis_core.field.M31 → aspis_core.field.M31 → Result Bool
  op6 : Result aspis_core.field.M31
  op7 : Result aspis_core.field.M31
  op8 : aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op9 : aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op10 : aspis_core.field.M31 → Result aspis_core.field.M31
  op11 : aspis_core.field.M31 → Result aspis_core.field.M31
  op12 : Std.Usize → Result (core.result.Result aspis_core.r0.domain.FibreIndex
        CoreError)
  op13 : (Slice aspis_core.field.M31) → Result ((alloc.vec.Vec aspis_core.field.M31)
        × aspis_core.field.M31)
  op14 : aspis_core.r0.domain.FibreIndex → Result aspis_core.field.M31
  op15 : aspis_core.r0.domain.FibreIndex → Result (aspis_core.r0.domain.Point
        aspis_core.field.M31)
  mapIterator : ∀ {B I F Item : Type}, core.iter.traits.iterator.Iterator I Item →
    core.ops.function.FnMut F Item B → core.iter.traits.iterator.Iterator (core.iter.adapters.map.Map I F) B

def verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut (ops : Ops CoreError)
  (c : verifier.QueryGeometry.for_range.closure_4.closure)
  (tupled_args : Std.Usize) :
  Result (aspis_core.field.M31 ×
    verifier.QueryGeometry.for_range.closure_4.closure)
  := do
  let (v, i) := c
  let i1 ← lift (Std.Usize.wrapping_mul 5#usize i)
  let i2 ← lift (Std.Usize.wrapping_add i1 tupled_args)
  let m ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.M31) v i2
  ok (m, c)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
def verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once (ops : Ops CoreError)
  (c : verifier.QueryGeometry.for_range.closure_4.closure) (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    (verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut ops)
      c i
  ok m

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
@[reducible]
def verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 (ops : Ops CoreError)
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_4.closure
  Std.Usize aspis_core.field.M31 := {
  call_once :=
    (verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once ops)
}

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
@[reducible]
def verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 (ops : Ops CoreError)
  : core.ops.function.FnMut verifier.QueryGeometry.for_range.closure_4.closure
  Std.Usize aspis_core.field.M31 := {
  FnOnceInst :=
    (verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 ops)
  call_mut :=
    (verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut ops)
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
def verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut (ops : Ops CoreError)
  (c : verifier.QueryGeometry.for_range.closure_4) (tupled_args : Std.Usize) :
  Result ((Array aspis_core.field.M31 5#usize) ×
    verifier.QueryGeometry.for_range.closure_4)
  := do
  let a ←
    ops.op0 5#usize
      (verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 ops)
      (c, tupled_args)
  ok (a, c)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
def verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once (ops : Ops CoreError)
  (c : verifier.QueryGeometry.for_range.closure_4) (i : Std.Usize) :
  Result (Array aspis_core.field.M31 5#usize)
  := do
  let (a, _) ←
    (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut ops)
      c i
  ok a

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
@[reducible]
def verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 (ops : Ops CoreError)
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_4
  Std.Usize (Array aspis_core.field.M31 5#usize) := {
  call_once :=
    (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once ops)
}

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
@[reducible]
def verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 (ops : Ops CoreError)
  : core.ops.function.FnMut verifier.QueryGeometry.for_range.closure_4
  Std.Usize (Array aspis_core.field.M31 5#usize) := {
  FnOnceInst :=
    (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 ops)
  call_mut :=
    (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut ops)
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
def verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut (ops : Ops CoreError)
  (c : verifier.QueryGeometry.for_range.closure_3)
  (tupled_args : aspis_core.field.M31) :
  Result (Bool × verifier.QueryGeometry.for_range.closure_3)
  := do
  let m ← ops.op6
  let b ← ops.op5 tupled_args m
  ok (b, c)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
def verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once (ops : Ops CoreError)
  (c : verifier.QueryGeometry.for_range.closure_3) (m : aspis_core.field.M31) :
  Result Bool
  := do
  let (b, _) ←
    (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut ops)
      c m
  ok b

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
@[reducible]
def verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool (ops : Ops CoreError)
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_3
  aspis_core.field.M31 Bool := {
  call_once :=
    (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once ops)
}

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
@[reducible]
def verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (ops : Ops CoreError)
  : core.ops.function.FnMut verifier.QueryGeometry.for_range.closure_3
  aspis_core.field.M31 Bool := {
  FnOnceInst :=
    (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool ops)
  call_mut :=
    (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut ops)
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#2}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 157:94-157:109 -/
def verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once (ops : Ops CoreError)
  (c : verifier.QueryGeometry.for_range.closure_2)
  (tupled_args : CoreError) :
  Result verifier.Error
  := do
  ok verifier.Error.Query

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#2}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 157:94-157:109 -/
@[reducible]
def verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError (ops : Ops CoreError)
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_2
  CoreError verifier.Error := {
  call_once :=
    (verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once ops)
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#1}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 156:92-156:107 -/
def verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once (ops : Ops CoreError)
  (c : verifier.QueryGeometry.for_range.closure_1)
  (tupled_args : CoreError) :
  Result verifier.Error
  := do
  ok verifier.Error.Query

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#1}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 156:92-156:107 -/
@[reducible]
def verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError (ops : Ops CoreError)
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_1
  CoreError verifier.Error := {
  call_once :=
    (verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once ops)
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 154:57-154:72 -/
def verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once (ops : Ops CoreError)
  (c : verifier.QueryGeometry.for_range.closure)
  (tupled_args : CoreError) :
  Result verifier.Error
  := do
  ok verifier.Error.Query

/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 154:57-154:72 -/
@[reducible]
def verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError (ops : Ops CoreError)
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure
  CoreError verifier.Error := {
  call_once :=
    (verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once ops)
}

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 171:8-174:9 -/
@[rust_loop_body]
def verifier.QueryGeometry.for_range_loop0_loop0.body (ops : Ops CoreError)
  (flat : alloc.vec.Vec aspis_core.field.M31)
  (prefixes : alloc.vec.Vec aspis_core.field.M31)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (suffix_inverse : aspis_core.field.M31)
  (flat_inverse : alloc.vec.Vec aspis_core.field.M31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × aspis_core.field.M31 × (alloc.vec.Vec
    aspis_core.field.M31)) (alloc.vec.Vec aspis_core.field.M31))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done flat_inverse)
  | some i =>
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) prefixes i
    let m1 ← ops.op9 suffix_inverse m
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat_inverse i
    let flat_inverse1 := index_mut_back m1
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.M31) flat i
    let suffix_inverse1 ← ops.op9 suffix_inverse m2
    ok (cont (iter1, suffix_inverse1, flat_inverse1))

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 171:8-174:9 -/
@[rust_loop]
def verifier.QueryGeometry.for_range_loop0_loop0 (ops : Ops CoreError)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (flat : alloc.vec.Vec aspis_core.field.M31)
  (prefixes : alloc.vec.Vec aspis_core.field.M31)
  (suffix_inverse : aspis_core.field.M31)
  (flat_inverse : alloc.vec.Vec aspis_core.field.M31) :
  Result (alloc.vec.Vec aspis_core.field.M31)
  := do
  loop
    (fun (iter1, suffix_inverse1, flat_inverse1) =>
      (verifier.QueryGeometry.for_range_loop0_loop0.body ops) flat prefixes iter1
      suffix_inverse1 flat_inverse1)
    (iter, suffix_inverse, flat_inverse)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 152:8-177:5 -/
@[rust_loop_body]
def verifier.QueryGeometry.for_range_loop0.body (ops : Ops CoreError)
  (start : Std.Usize) (iter : core.slice.iter.Iter Std.U32)
  (line_z_values : alloc.vec.Vec aspis_core.field.M31)
  (flat : alloc.vec.Vec aspis_core.field.M31) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U32) × (alloc.vec.Vec
    aspis_core.field.M31) × (alloc.vec.Vec aspis_core.field.M31))
    (core.result.Result verifier.QueryGeometry verifier.Error))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none =>
    let b ← ops.op4 Global flat
    if b
    then
      ok (done (core.result.Result.Ok
        {
          start,
          inverses := (alloc.vec.Vec.new (Array aspis_core.field.M31 5#usize)),
          line_z := line_z_values
        }))
    else
      let s := alloc.vec.Vec.deref flat
      let (prefixes, product) ← ops.op13 s
      let suffix_inverse ← ops.op11 product
      let i := alloc.vec.Vec.len flat
      let flat_inverse := alloc.vec.Vec.with_capacity aspis_core.field.M31 i
      let i1 := alloc.vec.Vec.len flat
      let m ← ops.op6
      let flat_inverse1 ←
        alloc.vec.Vec.resize core.marker.CopyU32.cloneInst
          flat_inverse i1 m
      let i2 := alloc.vec.Vec.len flat
      let iter2 ←
        core.iter.traits.iterator.Iterator.rev.trait_default
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (core.ops.range.Range.Insts.DoubleEndedIterator
          core.iter.range.StepUsize) { start := 0#usize, «end» := i2 }
      let flat_inverse2 ←
        (verifier.QueryGeometry.for_range_loop0_loop0 ops) iter2 flat prefixes
          suffix_inverse flat_inverse1
      let i3 := alloc.vec.Vec.len line_z_values
      let m1 ←
        ops.op1
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 ops)
          { start := 0#usize, «end» := i3 } flat_inverse2
      let inverses ←
        core.iter.traits.iterator.Iterator.collect.default
          (ops.mapIterator
          (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
          (verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 ops))
          (core.iter.traits.collect.FromIteratorVec (Array aspis_core.field.M31
          5#usize)) m1
      ok (done (core.result.Result.Ok
        { start, inverses, line_z := line_z_values }))
  | some query =>
    let u ← lift (UScalar.cast .Usize query)
    let r ← ops.op12 u
    let r1 ←
      ops.op2
        (verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError ops)
        r ()
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let p ← ops.op15 val
      let i ← u / 4#usize
      let i1 ← lift (Std.Usize.wrapping_mul i 4#usize)
      let r2 ← ops.op12 i1
      let r3 ←
        ops.op2
          (verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError ops)
          r2 ()
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let line_x ← ops.op14 val1
        let i2 ← lift (Std.Usize.wrapping_mul i 4#usize)
        let i3 ← lift (Std.Usize.wrapping_add i2 3#usize)
        let r4 ← ops.op12 i3
        let r5 ←
          ops.op2
            (verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError ops)
            r4 ()
        let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r5
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let line_y ← ops.op14 val2
          let m ← ops.op9 line_x line_x
          let m1 ← ops.op10 m
          let m2 ← ops.op7
          let line_z ← ops.op8 m1 m2
          let s ←
            lift (Array.to_slice
              (Array.make 5#usize [ p.x, p.y, line_x, line_y, line_z ]))
          let i4 ← core.slice.Slice.iter s
          let (b, _) ←
            ops.op3
              (verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool ops)
              i4 ()
          if b
          then ok (done (core.result.Result.Err verifier.Error.Query))
          else
            let s1 ←
              lift (Array.to_slice
                (Array.make 5#usize [ p.x, p.y, line_x, line_y, line_z ]))
            let flat1 ←
              alloc.vec.Vec.extend_from_slice
                core.marker.CopyU32.cloneInst flat s1
            let line_z_values1 ← alloc.vec.Vec.push line_z_values line_z
            ok (cont (iter1, line_z_values1, flat1))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r6 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              verifier.QueryGeometry (core.convert.FromSame verifier.Error)
              residual
          ok (done r6)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r4 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            verifier.QueryGeometry (core.convert.FromSame verifier.Error)
            residual
        ok (done r4)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r2 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          verifier.QueryGeometry (core.convert.FromSame verifier.Error)
          residual
      ok (done r2)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 152:8-177:5 -/
@[rust_loop]
def verifier.QueryGeometry.for_range_loop0 (ops : Ops CoreError)
  (iter : core.slice.iter.Iter Std.U32) (start : Std.Usize)
  (line_z_values : alloc.vec.Vec aspis_core.field.M31)
  (flat : alloc.vec.Vec aspis_core.field.M31) :
  Result (core.result.Result verifier.QueryGeometry verifier.Error)
  := do
  loop
    (fun (iter1, line_z_values1, flat1) =>
      (verifier.QueryGeometry.for_range_loop0.body ops) start iter1 line_z_values1
      flat1)
    (iter, line_z_values, flat)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 148:4-177:5 -/
def verifier.QueryGeometry.for_range (ops : Ops CoreError)
  (queries : Array Std.U32 22#usize) (start : Std.Usize) (end1 : Std.Usize) :
  Result (core.result.Result verifier.QueryGeometry verifier.Error)
  := do
  if start > end1
  then ok (core.result.Result.Err verifier.Error.Query)
  else
    let s ← lift (Array.to_slice queries)
    let i := Slice.len s
    if end1 > i
    then ok (core.result.Result.Err verifier.Error.Query)
    else
      let i1 ← lift (Std.Usize.wrapping_sub end1 start)
      let line_z_values := alloc.vec.Vec.with_capacity aspis_core.field.M31 i1
      let i2 ← lift (Std.Usize.wrapping_sub end1 start)
      let i3 ← lift (Std.Usize.wrapping_mul i2 5#usize)
      let flat := alloc.vec.Vec.with_capacity aspis_core.field.M31 i3
      let s1 ←
        core.array.Array.index (core.ops.index.IndexSlice
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U32)) queries
          { start, «end» := end1 }
      let iter ←
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
          s1
      (verifier.QueryGeometry.for_range_loop0 ops) iter start line_z_values flat


#print axioms verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
#print axioms verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
#print axioms verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
#print axioms verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31
#print axioms verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut
#print axioms verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once
#print axioms verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315
#print axioms verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315
#print axioms verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut
#print axioms verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once
#print axioms verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool
#print axioms verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
#print axioms verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
#print axioms verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError
#print axioms verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
#print axioms verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
#print axioms verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
#print axioms verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
#print axioms verifier.QueryGeometry.for_range_loop0_loop0.body
#print axioms verifier.QueryGeometry.for_range_loop0_loop0
#print axioms verifier.QueryGeometry.for_range_loop0.body
#print axioms verifier.QueryGeometry.for_range_loop0
#print axioms verifier.QueryGeometry.for_range
end AspisR1.Port3_NativeGeometryBody
end
