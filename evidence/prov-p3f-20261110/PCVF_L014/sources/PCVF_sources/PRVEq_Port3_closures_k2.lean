-- PCVF_ item 2 (Port3_NativeGeometryBody closure class). Fresh text: OFF emission PCVF_E005 (PCQD E011 spec, no overflow checks,
-- extended Aeneas, frozen 4bb3b3f), closure definitions of QueryGeometry::for_range, external axioms of the emission replaced by Ext.
-- Gate: AspisR1.Port3_NativeGeometryBody (takes ops : Ops CoreError). RESULT CLASS: CONDITIONAL_ON_BINDING for the definitions that use ops
-- (from_fn, M31 zero, M31 eq bound to the emission's externals); closure_4.closure and closure/closure_1/closure_2 need no binding.
import Aeneas
import Port3_NativeGeometryBody
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1.Port3_NativeGeometryBody
namespace PRVFresh_k2

inductive aspis_core.r0.Error where
| IndexOutOfRange : aspis_core.r0.Error
| WrongLength : aspis_core.r0.Error
| ZeroDenominator : aspis_core.r0.Error
| Allocation : aspis_core.r0.Error
| NonCanonical : aspis_core.r0.Error
| WrongField : aspis_core.r0.Error
| InvalidPoints : aspis_core.r0.Error
| QuotientNotInImage : aspis_core.r0.Error
| RankDeficient : aspis_core.r0.Error

structure Ext where
  from_fn : ∀ {T : Type} {F : Type} (N : Std.Usize) (opsfunctionFnMutFTupleUsizeTInst : core.ops.function.FnMut F Std.Usize T), F → Result (Array T N)
  zero : Result aspis_core.field.M31
  eq : aspis_core.field.M31 → aspis_core.field.M31 → Result Bool

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
def
  verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
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
def
  verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
  (c : verifier.QueryGeometry.for_range.closure_4.closure) (i : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let (m, _) ←
    verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
      c i
  ok m


/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnOnce<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_4.closure
  Std.Usize aspis_core.field.M31 := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once
}


/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::{impl core::ops::function::FnMut<(usize,), aspis_core::field::M31> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4::closure<'_0, '_1>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:74-175:96 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31
  : core.ops.function.FnMut verifier.QueryGeometry.for_range.closure_4.closure
  Std.Usize aspis_core.field.M31 := {
  FnOnceInst :=
    verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31
  call_mut :=
    verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut
}


/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
def
  verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut (x : Ext)
  (c : verifier.QueryGeometry.for_range.closure_4) (tupled_args : Std.Usize) :
  Result ((Array aspis_core.field.M31 5#usize) ×
    verifier.QueryGeometry.for_range.closure_4)
  := do
  let a ←
    x.from_fn 5#usize
      verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31
      (c, tupled_args)
  ok (a, c)


/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
def
  verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once (x : Ext)
  (c : verifier.QueryGeometry.for_range.closure_4) (i : Std.Usize) :
  Result (Array aspis_core.field.M31 5#usize)
  := do
  let (a, _) ←
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut x
      c i
  ok a


/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 (x : Ext)
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_4
  Std.Usize (Array aspis_core.field.M31 5#usize) := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once x
}


/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(usize,), [aspis_core::field::M31; 5usize]> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#4<'_0>}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 175:50-175:97 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 (x : Ext)
  : core.ops.function.FnMut verifier.QueryGeometry.for_range.closure_4
  Std.Usize (Array aspis_core.field.M31 5#usize) := {
  FnOnceInst :=
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 x
  call_mut :=
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut x
}


/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}::call_mut]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
def
  verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut (x : Ext)
  (c : verifier.QueryGeometry.for_range.closure_3)
  (tupled_args : aspis_core.field.M31) :
  Result (Bool × verifier.QueryGeometry.for_range.closure_3)
  := do
  let m ← x.zero
  let b ← x.eq tupled_args m
  ok (b, c)


/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
def
  verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once (x : Ext)
  (c : verifier.QueryGeometry.for_range.closure_3) (m : aspis_core.field.M31) :
  Result Bool
  := do
  let (b, _) ←
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut x
      c m
  ok b


/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool (x : Ext)
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_3
  aspis_core.field.M31 Bool := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once x
}


/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnMut<(&'_ aspis_core::field::M31,), bool> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#3}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 160:33-160:49 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (x : Ext)
  : core.ops.function.FnMut verifier.QueryGeometry.for_range.closure_3
  aspis_core.field.M31 Bool := {
  FnOnceInst :=
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool x
  call_mut :=
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut x
}


/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#2}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 157:94-157:109 -/
def
  verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  (c : verifier.QueryGeometry.for_range.closure_2)
  (tupled_args : aspis_core.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Query


/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#2}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 157:94-157:109 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_2
  aspis_core.r0.Error verifier.Error := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
}


/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#1}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 156:92-156:107 -/
def
  verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  (c : verifier.QueryGeometry.for_range.closure_1)
  (tupled_args : aspis_core.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Query


/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure#1}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 156:92-156:107 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure_1
  aspis_core.r0.Error verifier.Error := {
  call_once :=
    verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
}


/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure}::call_once]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 154:57-154:72 -/
def
  verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
  (c : verifier.QueryGeometry.for_range.closure)
  (tupled_args : aspis_core.r0.Error) :
  Result verifier.Error
  := do
  ok verifier.Error.Query


/-- Trait implementation: [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::{impl core::ops::function::FnOnce<(aspis_core::r0::Error,), aspis_r1_cost_probe::verifier::Error> for aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::QueryGeometry}::for_range::closure}]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 154:57-154:72 -/
@[reducible]
def
  verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
  : core.ops.function.FnOnce verifier.QueryGeometry.for_range.closure
  aspis_core.r0.Error verifier.Error := {
  call_once :=
    verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
}


end PRVFresh_k2
end AspisR1.Port3_NativeGeometryBody

namespace PRVEq.Port3_k2
open AspisR1.Port3_NativeGeometryBody
variable {CoreError : Type}

/-- The binding of the gate record fields used by this class to the emission's externals. -/
structure Bound (ops : Ops CoreError) (x : PRVFresh_k2.Ext) : Prop where
  h0 : ∀ {T F : Type} (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T) (f : F), ops.op0 N inst f = x.from_fn N inst f
  h5 : ops.op5 = x.eq
  h6 : ops.op6 = x.zero

theorem eq_0 (ops : Ops CoreError) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut; rfl)
theorem eq_1 (ops : Ops CoreError) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once; rfl)
theorem eq_2 (ops : Ops CoreError) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31; rfl)
theorem eq_3 (ops : Ops CoreError) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31; rfl)
theorem eq_4 {ops : Ops CoreError} {x : PRVFresh_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut ops := by
  first | rfl | (funext _ _; unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_5 {ops : Ops CoreError} {x : PRVFresh_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once ops := by
  first | rfl | (funext _ _; unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_6 {ops : Ops CoreError} {x : PRVFresh_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 ops := by
  first | rfl | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_7 {ops : Ops CoreError} {x : PRVFresh_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 ops := by
  first | rfl | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_8 {ops : Ops CoreError} {x : PRVFresh_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut ops := by
  first | rfl | (funext _ _; unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [eq_7 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_9 {ops : Ops CoreError} {x : PRVFresh_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once ops := by
  first | rfl | (funext _ _; unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [eq_7 b] | rw [eq_8 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_10 {ops : Ops CoreError} {x : PRVFresh_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool ops := by
  first | rfl | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [eq_7 b] | rw [eq_8 b] | rw [eq_9 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_11 {ops : Ops CoreError} {x : PRVFresh_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool ops := by
  first | rfl | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [eq_7 b] | rw [eq_8 b] | rw [eq_9 b] | rw [eq_10 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_12 (ops : Ops PRVFresh_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once; rfl)
theorem eq_13 (ops : Ops PRVFresh_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError; rfl)
theorem eq_14 (ops : Ops PRVFresh_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once; rfl)
theorem eq_15 (ops : Ops PRVFresh_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError; rfl)
theorem eq_16 (ops : Ops PRVFresh_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once; rfl)
theorem eq_17 (ops : Ops PRVFresh_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_k2.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError; rfl)

end PRVEq.Port3_k2

#print axioms PRVEq.Port3_k2.eq_0
#print axioms PRVEq.Port3_k2.eq_1
#print axioms PRVEq.Port3_k2.eq_2
#print axioms PRVEq.Port3_k2.eq_3
#print axioms PRVEq.Port3_k2.eq_4
#print axioms PRVEq.Port3_k2.eq_5
#print axioms PRVEq.Port3_k2.eq_6
#print axioms PRVEq.Port3_k2.eq_7
#print axioms PRVEq.Port3_k2.eq_8
#print axioms PRVEq.Port3_k2.eq_9
#print axioms PRVEq.Port3_k2.eq_10
#print axioms PRVEq.Port3_k2.eq_11
#print axioms PRVEq.Port3_k2.eq_12
#print axioms PRVEq.Port3_k2.eq_13
#print axioms PRVEq.Port3_k2.eq_14
#print axioms PRVEq.Port3_k2.eq_15
#print axioms PRVEq.Port3_k2.eq_16
#print axioms PRVEq.Port3_k2.eq_17
