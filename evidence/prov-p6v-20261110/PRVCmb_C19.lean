-- PCXE combined-import bundle PRVCmb_C19: exact file texts (import lines hoisted), declared names renamed by PCXE_rename.py tag C19_Fjj (rules PCXB-C2, PCXE-C4): PRVEq_Port3_closures_k2.lean, PRVEq_Port5Q2_ReaderWeights_k1.lean, PRVEq_S1NativeCompactModelV1_okor_f1.lean, PRVEq_AspisR1EbyKFinish_Funs_n1.lean, PRVEq_AspisR1QueryGeometryActual_Funs_m1.lean, PRVEq_CurrentCompactCallerModelV1_n1.lean, PRVEq_CurrentCompactCallerModelV1_n2.lean, PRVEq_FinishCandidateExplicitOps_n1.lean, PRVEq_PCVH_R1CandidateWideParserSource_k1.lean, PRVEq_Stage2ContinuationTypes_n2.lean, PRVEq_NMT_stage1_owned_i1.lean, PRVEq_Port23PUSH_Source_i1.lean, PRVEq_RPz7_FIp_NativeDots_i9.lean, PRVEq_S1NativeCompactExpand_i1.lean
import Aeneas
import Port3_NativeGeometryBody
import Port5Q2_ReaderWeights
import S1NativeCompactModelV1
import AspisR1EbyKFinish.Funs
import AspisR1QueryGeometryActual.Funs
import CurrentCompactCallerModelV1
import FinishCandidateExplicitOps
import R1CandidateWideParserSource
import Stage2ContinuationTypes
import NMT_stage1_owned.Funs
import Port23PUSH_Source
import RPz7_FIp_NativeDots
import RPz7_FIp_DotDecode
section PRVBundle_0
-- PCVF_ item 2 (Port3_NativeGeometryBody closure class). Fresh text: OFF emission PCVF_E005 (PCQD E011 spec, no overflow checks,
-- extended Aeneas, frozen 4bb3b3f), closure definitions of QueryGeometry::for_range, external axioms of the emission replaced by Ext.
-- Gate: AspisR1.Port3_NativeGeometryBody (takes ops : Ops CoreError). RESULT CLASS: CONDITIONAL_ON_BINDING for the definitions that use ops
-- (from_fn, M31 zero, M31 eq bound to the emission's externals); closure_4.closure and closure/closure_1/closure_2 need no binding.
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace AspisR1.Port3_NativeGeometryBody
namespace PRVFresh_C19_F00_k2

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
| Parse : aspis_core.r0.Error
| Semantic : aspis_core.r0.Error
| Schedule : aspis_core.r0.Error
| Sampler : aspis_core.r0.Error
| Commitment : aspis_core.r0.Error
| Authentication : aspis_core.r0.Error
| V1 : aspis_core.r0.Error
| V2 : aspis_core.r0.Error

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


end PRVFresh_C19_F00_k2
end AspisR1.Port3_NativeGeometryBody

namespace PRVEq.C19_F00.Port3_k2
open AspisR1.Port3_NativeGeometryBody
variable {CoreError : Type}

/-- The binding of the gate record fields used by this class to the emission's externals. -/
structure Bound (ops : Ops CoreError) (x : PRVFresh_C19_F00_k2.Ext) : Prop where
  h0 : ∀ {T F : Type} (N : Std.Usize) (inst : core.ops.function.FnMut F Std.Usize T) (f : F), ops.op0 N inst f = x.from_fn N inst f
  h5 : ops.op5 = x.eq
  h6 : ops.op6 = x.zero

theorem eq_0 (ops : Ops CoreError) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31.call_mut; rfl)
theorem eq_1 (ops : Ops CoreError) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31.call_once; rfl)
theorem eq_2 (ops : Ops CoreError) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31 AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeM31; rfl)
theorem eq_3 (ops : Ops CoreError) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31 AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.closure.Insts.CoreOpsFunctionFnMutTupleUsizeM31; rfl)
theorem eq_4 {ops : Ops CoreError} {x : PRVFresh_C19_F00_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut ops := by
  first | rfl | (funext _ _; unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_5 {ops : Ops CoreError} {x : PRVFresh_C19_F00_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once ops := by
  first | rfl | (funext _ _; unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_6 {ops : Ops CoreError} {x : PRVFresh_C19_F00_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 ops := by
  first | rfl | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_7 {ops : Ops CoreError} {x : PRVFresh_C19_F00_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 ops := by
  first | rfl | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_8 {ops : Ops CoreError} {x : PRVFresh_C19_F00_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut ops := by
  first | rfl | (funext _ _; unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [eq_7 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_9 {ops : Ops CoreError} {x : PRVFresh_C19_F00_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once ops := by
  first | rfl | (funext _ _; unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [eq_7 b] | rw [eq_8 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_10 {ops : Ops CoreError} {x : PRVFresh_C19_F00_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool ops := by
  first | rfl | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [eq_7 b] | rw [eq_8 b] | rw [eq_9 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_11 {ops : Ops CoreError} {x : PRVFresh_C19_F00_k2.Ext} (b : Bound ops x) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool x = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool ops := by
  first | rfl | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool; repeat (first | rw [eq_0 b] | rw [eq_1 b] | rw [eq_2 b] | rw [eq_3 b] | rw [eq_4 b] | rw [eq_5 b] | rw [eq_6 b] | rw [eq_7 b] | rw [eq_8 b] | rw [eq_9 b] | rw [eq_10 b] | rw [b.h6] | rw [b.h5] | simp only [b.h0]); try rfl)
theorem eq_12 (ops : Ops PRVFresh_C19_F00_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once; rfl)
theorem eq_13 (ops : Ops PRVFresh_C19_F00_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError; rfl)
theorem eq_14 (ops : Ops PRVFresh_C19_F00_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once; rfl)
theorem eq_15 (ops : Ops PRVFresh_C19_F00_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError; rfl)
theorem eq_16 (ops : Ops PRVFresh_C19_F00_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once; rfl)
theorem eq_17 (ops : Ops PRVFresh_C19_F00_k2.aspis_core.r0.Error) :
    AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError = AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError ops := by
  first | rfl | (funext _ _; rfl) | (unfold AspisR1.Port3_NativeGeometryBody.PRVFresh_C19_F00_k2.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError AspisR1.Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError; rfl)

end PRVEq.C19_F00.Port3_k2

#print axioms PRVEq.C19_F00.Port3_k2.eq_0
#print axioms PRVEq.C19_F00.Port3_k2.eq_1
#print axioms PRVEq.C19_F00.Port3_k2.eq_2
#print axioms PRVEq.C19_F00.Port3_k2.eq_3
#print axioms PRVEq.C19_F00.Port3_k2.eq_4
#print axioms PRVEq.C19_F00.Port3_k2.eq_5
#print axioms PRVEq.C19_F00.Port3_k2.eq_6
#print axioms PRVEq.C19_F00.Port3_k2.eq_7
#print axioms PRVEq.C19_F00.Port3_k2.eq_8
#print axioms PRVEq.C19_F00.Port3_k2.eq_9
#print axioms PRVEq.C19_F00.Port3_k2.eq_10
#print axioms PRVEq.C19_F00.Port3_k2.eq_11
#print axioms PRVEq.C19_F00.Port3_k2.eq_12
#print axioms PRVEq.C19_F00.Port3_k2.eq_13
#print axioms PRVEq.C19_F00.Port3_k2.eq_14
#print axioms PRVEq.C19_F00.Port3_k2.eq_15
#print axioms PRVEq.C19_F00.Port3_k2.eq_16
#print axioms PRVEq.C19_F00.Port3_k2.eq_17

end
end PRVBundle_0
section PRVBundle_1
-- PCVF_ item 2 (parametric record Port5Q2_ReaderWeights: ReadK parameter + hand IterMut model). Statements: fresh = gate.
-- Fresh text: PCQD_E034 emission (prov-p1g-20261109/PCQD_E034_emitted/raw/PCQD_d11b, Aeneas b59d5188-extended, overflow ON),
-- declarations Reader.raw, Reader.k, read_checkpoint_weights{,_loop,_loop.body} (+ ok_or). Types (M31, CM31, QM31, Error, Reader) are read as the
-- gate's declarations of the same name (same structure text; only the discriminant attribute differs). Externals of the emission
-- (axioms there): QM31.from_le_bytes and MutAVec..IterMut.into_iter (at A := Global) are fields of `Ext`.
-- RESULT CLASS: CONDITIONAL_ON_BINDING. The gate takes `read : ReadK` and uses the hand model `intoIter`; the equality is
-- at read := fresh Reader.k and with the Vec-IterMut external bound to the hand model (hypothesis hInto: the core slice iterator model).
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1.Port5Q2_ReaderWeights
namespace PRVFresh_C19_F01_k1

structure Ext where
  from_le_bytes : (Slice Std.U8) → Result (Option aspis_core.field.QM31)
  into_iter : (alloc.vec.Vec aspis_core.field.QM31) →
    Result ((core.slice.iter.IterMut aspis_core.field.QM31) × (core.slice.iter.IterMut aspis_core.field.QM31 → alloc.vec.Vec aspis_core.field.QM31))

/-- [core::option::{core::option::Option<T>}::ok_or]:
    Source: '/rustc/library/core/src/option.rs', lines 1334:4-1334:73
    Name pattern: [core::option::{core::option::Option<@T>}::ok_or]
    Visibility: public -/
@[rust_fun "core::option::{core::option::Option<@T>}::ok_or"]
def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::raw]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 344:4-344:116 -/
def verifier.Reader.raw
  (N : Std.Usize) (self : verifier.Reader) :
  Result ((Array Std.U8 N) × verifier.Reader)
  := do
  let i ← self.«at» + N
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      Std.U8) self.bytes { start := self.«at», «end» := i }
  let r ← core.array.TryFromArrayCopySlice.try_from N core.marker.CopyU8 s
  let b ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  ok (b, { self with «at» := i })

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::Reader<'a>}::k]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 347:4-347:98 -/
def verifier.Reader.k (x : Ext)
  (self : verifier.Reader) :
  Result ((core.result.Result aspis_core.field.QM31 verifier.Error) ×
    verifier.Reader)
  := do
  let (a, self1) ← verifier.Reader.raw 16#usize self
  let s ← lift (Array.to_slice a)
  let o ← x.from_le_bytes s
  let r ← core.option.Option.ok_or o verifier.Error.Checkpoint
  ok (r, self1)

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 364:4-371:1 -/
@[rust_loop_body]
def verifier.read_checkpoint_weights_loop.body (x : Ext)
  (bytes : Slice Std.U8) (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (at1 : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.IterMut aspis_core.field.QM31) ×
    (core.slice.iter.IterMut aspis_core.field.QM31 → core.slice.iter.IterMut
    aspis_core.field.QM31) × Std.Usize) (Std.Usize × (Option
    (core.result.Result ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
    verifier.Error)) × (core.slice.iter.IterMut aspis_core.field.QM31)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => let im := next_back iter1 none
            ok (done (at1, none, back im))
  | some _ =>
    let (r, reader) ← verifier.Reader.k x { bytes, «at» := at1 }
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      ok (cont (iter1, fun im => let im1 := next_back im (some val)
                                 back im1, reader.«at»))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
          (core.convert.FromSame verifier.Error) residual
      let im := next_back iter1 o
      ok (done (at1, some r1, back im))

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 364:4-371:1 -/
@[rust_loop]
def verifier.read_checkpoint_weights_loop (x : Ext)
  (iter : core.slice.iter.IterMut aspis_core.field.QM31)
  (back : core.slice.iter.IterMut aspis_core.field.QM31 →
  core.slice.iter.IterMut aspis_core.field.QM31) (bytes : Slice Std.U8)
  (at1 : Std.Usize) :
  Result (Std.Usize × (Option (core.result.Result ((alloc.vec.Vec
    aspis_core.field.QM31) × Std.Usize) verifier.Error)) ×
    (core.slice.iter.IterMut aspis_core.field.QM31))
  := do
  loop
    (fun (iter1, back1, at2) => verifier.read_checkpoint_weights_loop.body x
      bytes iter1 back1 at2)
    (iter, back, at1)

/-- [aspis_r1_cost_probe::verifier::read_checkpoint_weights]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 363:0-371:1 -/
def verifier.read_checkpoint_weights (x : Ext)
  (bytes : Slice Std.U8) (at1 : Std.Usize)
  (weights : alloc.vec.Vec aspis_core.field.QM31) :
  Result (core.result.Result ((alloc.vec.Vec aspis_core.field.QM31) ×
    Std.Usize) verifier.Error)
  := do
  let (iter, into_iter_back) ← x.into_iter weights
  let (at2, pending_return, back) ←
    verifier.read_checkpoint_weights_loop x iter (fun im => im) bytes at1
  match pending_return with
  | none =>
    let weights1 := into_iter_back back
    ok (core.result.Result.Ok (weights1, at2))
  | some r => ok r


end PRVFresh_C19_F01_k1
end AspisR1.Port5Q2_ReaderWeights

namespace PRVEq.C19_F01.Port5Q2_k1
open AspisR1.Port5Q2_ReaderWeights

theorem loop_body_eq (x : PRVFresh_C19_F01_k1.Ext) :
    PRVFresh_C19_F01_k1.verifier.read_checkpoint_weights_loop.body x =
    AspisR1.Port5Q2_ReaderWeights.weights_loop.body (PRVFresh_C19_F01_k1.verifier.Reader.k x) := rfl

theorem loop_eq (x : PRVFresh_C19_F01_k1.Ext) :
    PRVFresh_C19_F01_k1.verifier.read_checkpoint_weights_loop x =
    AspisR1.Port5Q2_ReaderWeights.weights_loop (PRVFresh_C19_F01_k1.verifier.Reader.k x) := rfl

/-- The only binding: the emission's Vec-IterMut external is the gate's hand model. -/
theorem weights_eq (x : PRVFresh_C19_F01_k1.Ext) (hInto : x.into_iter = AspisR1.Port5Q2_ReaderWeights.intoIter) :
    PRVFresh_C19_F01_k1.verifier.read_checkpoint_weights x =
    AspisR1.Port5Q2_ReaderWeights.weights (PRVFresh_C19_F01_k1.verifier.Reader.k x) := by
  funext bytes at1 w
  unfold PRVFresh_C19_F01_k1.verifier.read_checkpoint_weights AspisR1.Port5Q2_ReaderWeights.weights
  rw [hInto]
  rfl

theorem binding_satisfiable : ∃ x : PRVFresh_C19_F01_k1.Ext, x.into_iter = AspisR1.Port5Q2_ReaderWeights.intoIter :=
  ⟨{ from_le_bytes := fun _ => .fail .panic, into_iter := AspisR1.Port5Q2_ReaderWeights.intoIter }, rfl⟩

end PRVEq.C19_F01.Port5Q2_k1

#print axioms PRVEq.C19_F01.Port5Q2_k1.loop_body_eq
#print axioms PRVEq.C19_F01.Port5Q2_k1.loop_eq
#print axioms PRVEq.C19_F01.Port5Q2_k1.weights_eq
#print axioms PRVEq.C19_F01.Port5Q2_k1.binding_satisfiable

end
end PRVBundle_1
section PRVBundle_2
-- PCVF_ item 5 (Option/Result helper class) / item 4 (Option.ok_or, S1NativeCompactModelV1).
-- Fresh text: PCQD_d04 emission (prov-p1g-20261109/PCQD_E013_emitted/raw/PCQD_d04, original Aeneas 959659a6, overflow ON), declaration core.option.Option.ok_or.
-- Statement is fresh = gate against the compiled gate constant AspisS1NativeCompact.core.option.Option.ok_or.
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisS1NativeCompact
namespace PRVFresh_C19_F02_S1NativeCompactModelV1

def core.option.Option.ok_or
  {T : Type} {E : Type} (self : Option T) (err : E) :
  Result (core.result.Result T E)
  := do
  match self with
  | none => ok (core.result.Result.Err err)
  | some v => ok (core.result.Result.Ok v)

end PRVFresh_C19_F02_S1NativeCompactModelV1
end AspisS1NativeCompact

theorem PRVEq.C19_F02.S1NativeCompactModelV1.core.option.Option.ok_or_f1 :
    @AspisS1NativeCompact.PRVFresh_C19_F02_S1NativeCompactModelV1.core.option.Option.ok_or =
    @AspisS1NativeCompact.core.option.Option.ok_or := by
  funext T E self err
  cases self <;> rfl
#print axioms PRVEq.C19_F02.S1NativeCompactModelV1.core.option.Option.ok_or_f1

end
end PRVBundle_2
section PRVBundle_3
-- GENERATED by PCVH_gen_equalities.py for gate module AspisR1EbyKFinish.Funs. Statements are against the gate constants of AspisR1EbyKFinish.Funs.
-- fresh emission: NMH_wide_decode -> PRVFresh_C19_F03_AspisR1EbyKFinish_Funs_n1; fresh source sha256 8a77c6278b0643da5b0fae48f1923133135d20d404d78da0a290caf0544ab2a3
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1EbyKFinish
namespace PRVFresh_C19_F03_AspisR1EbyKFinish_Funs_n1

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_limbs]:
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 207:4-235:5
    Visibility: public -/
def field.wide_exact.WideExact.from_limbs
  (limbs : Array Std.U32 8#usize) :
  Result (Option field.wide_exact.WideExact)
  := do
  let i ← Array.index_usize limbs 0#usize
  if i >= field.P
  then ok none
  else
    let i1 ← Array.index_usize limbs 1#usize
    if i1 >= field.P
    then ok none
    else
      let i2 ← Array.index_usize limbs 2#usize
      if i2 >= field.P
      then ok none
      else
        let i3 ← Array.index_usize limbs 3#usize
        if i3 >= field.P
        then ok none
        else
          let i4 ← Array.index_usize limbs 4#usize
          if i4 >= field.P
          then ok none
          else
            let i5 ← Array.index_usize limbs 5#usize
            if i5 >= field.P
            then ok none
            else
              let i6 ← Array.index_usize limbs 6#usize
              if i6 >= field.P
              then ok none
              else
                let i7 ← Array.index_usize limbs 7#usize
                if i7 >= field.P
                then ok none
                else
                  ok (some
                    {
                      c0 :=
                        { c0 := { a := i, b := i1 }, c1 := { a := i2, b := i3 }
                        },
                      c1 :=
                        {
                          c0 := { a := i4, b := i5 },
                          c1 := { a := i6, b := i7 }
                        }
                    })

end PRVFresh_C19_F03_AspisR1EbyKFinish_Funs_n1
end AspisR1EbyKFinish

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F03.AspisR1EbyKFinish.Funs_n1.field.P : @AspisR1EbyKFinish.PRVFresh_C19_F03_AspisR1EbyKFinish_Funs_n1.field.P = @AspisR1EbyKFinish.field.P := by
  first | (trace "PRV-S1 PRVEq.C19_F03.AspisR1EbyKFinish.Funs_n1.field.P"; rfl) | (trace "PRV-S2 PRVEq.C19_F03.AspisR1EbyKFinish.Funs_n1.field.P"; delta AspisR1EbyKFinish.PRVFresh_C19_F03_AspisR1EbyKFinish_Funs_n1.field.P AspisR1EbyKFinish.field.P; try rfl; done)
#print axioms PRVEq.C19_F03.AspisR1EbyKFinish.Funs_n1.field.P

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F03.AspisR1EbyKFinish.Funs_n1.field.wide_exact.WideExact.from_limbs : @AspisR1EbyKFinish.PRVFresh_C19_F03_AspisR1EbyKFinish_Funs_n1.field.wide_exact.WideExact.from_limbs = @AspisR1EbyKFinish.field.wide_exact.WideExact.from_limbs := by
  first | (trace "PRV-S1 PRVEq.C19_F03.AspisR1EbyKFinish.Funs_n1.field.wide_exact.WideExact.from_limbs"; rfl) | (trace "PRV-S2 PRVEq.C19_F03.AspisR1EbyKFinish.Funs_n1.field.wide_exact.WideExact.from_limbs"; delta AspisR1EbyKFinish.PRVFresh_C19_F03_AspisR1EbyKFinish_Funs_n1.field.wide_exact.WideExact.from_limbs AspisR1EbyKFinish.field.wide_exact.WideExact.from_limbs; try simp only [PRVEq.C19_F03.AspisR1EbyKFinish.Funs_n1.field.P]; try rfl; done)
#print axioms PRVEq.C19_F03.AspisR1EbyKFinish.Funs_n1.field.wide_exact.WideExact.from_limbs


end PRVBundle_3
section PRVBundle_4
-- GENERATED by PCVH_gen_equalities.py for gate module AspisR1QueryGeometryActual.Funs. Statements are against the gate constants of AspisR1QueryGeometryActual.Funs.
-- fresh emission: PCQD_d07 -> PRVFresh_C19_F04_AspisR1QueryGeometryActual_Funs_m1; fresh source sha256 720f1c96365a1ef717296080ff60555d8c0f616847175e154549d19a5f9d0b5e
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1QueryGeometryActual
namespace PRVFresh_C19_F04_AspisR1QueryGeometryActual_Funs_m1

/-- [aspis_r1_cost_probe::fast_domain::TABLE_A]
    Source: 'crates/aspis-r1-cost-probe/src/fast_domain.rs', lines 13:0-142:2 -/
@[global_simps, irreducible]
def fast_domain.TABLE_A : Array (Std.U32 × Std.U32) 512#usize :=
  Array.make 512#usize [
    (1022251061#u32, 788094511#u32), (788094511#u32, 1125232586#u32),
    (1462922215#u32, 117240331#u32), (117240331#u32, 684561432#u32),
    (479936188#u32, 217587789#u32), (217587789#u32, 1667547459#u32),
    (797223315#u32, 1892184156#u32), (1892184156#u32, 1350260332#u32),
    (1601663285#u32, 2022005567#u32), (2022005567#u32, 545820362#u32),
    (1715132412#u32, 1963268365#u32), (1963268365#u32, 432351235#u32),
    (1329069890#u32, 1640136239#u32), (1640136239#u32, 818413757#u32),
    (1052324090#u32, 1064735370#u32), (1064735370#u32, 1095159557#u32),
    (119109612#u32, 1742172267#u32), (1742172267#u32, 2028374035#u32),
    (1949036272#u32, 2084561085#u32), (2084561085#u32, 198447375#u32),
    (1276985988#u32, 456990464#u32), (456990464#u32, 870497659#u32),
    (818046810#u32, 1849544479#u32), (1849544479#u32, 1329436837#u32),
    (1068288753#u32, 675427495#u32), (675427495#u32, 1079194894#u32),
    (2144102382#u32, 886761621#u32), (886761621#u32, 3381265#u32),
    (1542630618#u32, 1177056098#u32), (1177056098#u32, 604853029#u32),
    (270443035#u32, 1665395253#u32), (1665395253#u32, 1877040612#u32),
    (1319895764#u32, 573785706#u32), (573785706#u32, 827587883#u32),
    (614428895#u32, 566940551#u32), (566940551#u32, 1533054752#u32),
    (1614159808#u32, 1309336248#u32), (1309336248#u32, 533323839#u32),
    (20753985#u32, 1635511764#u32), (1635511764#u32, 2126729662#u32),
    (1685341984#u32, 359481912#u32), (359481912#u32, 462141663#u32),
    (1152154081#u32, 2106306808#u32), (2106306808#u32, 995329566#u32),
    (638582271#u32, 300788326#u32), (300788326#u32, 1508901376#u32),
    (1412610045#u32, 1446210525#u32), (1446210525#u32, 734873602#u32),
    (1747362177#u32, 1031300071#u32), (1031300071#u32, 400121470#u32),
    (45393311#u32, 1630721361#u32), (1630721361#u32, 2102090336#u32),
    (628786761#u32, 140902127#u32), (140902127#u32, 1518696886#u32),
    (1117531616#u32, 1012065003#u32), (1012065003#u32, 1029952031#u32),
    (320524274#u32, 1536842560#u32), (1536842560#u32, 1826959373#u32),
    (362376885#u32, 1168590975#u32), (1168590975#u32, 1785106762#u32),
    (1108016105#u32, 252024370#u32), (252024370#u32, 1039467542#u32),
    (1225642256#u32, 1294224634#u32), (1294224634#u32, 921841391#u32),
    (400584953#u32, 469433912#u32), (469433912#u32, 1746898694#u32),
    (932754395#u32, 1184859162#u32), (1184859162#u32, 1214729252#u32),
    (1636215277#u32, 965201017#u32), (965201017#u32, 511268370#u32),
    (993237774#u32, 289789953#u32), (289789953#u32, 1154245873#u32),
    (1844375598#u32, 1823771499#u32), (1823771499#u32, 303108049#u32),
    (1036868259#u32, 1302232773#u32), (1302232773#u32, 1110615388#u32),
    (1489475671#u32, 1590331411#u32), (1590331411#u32, 658007976#u32),
    (271955858#u32, 2011039234#u32), (2011039234#u32, 1875527789#u32),
    (494932510#u32, 292984488#u32), (292984488#u32, 1652551137#u32),
    (1415786230#u32, 1111815158#u32), (1111815158#u32, 731697417#u32),
    (1150508049#u32, 626837953#u32), (626837953#u32, 996975598#u32),
    (317286896#u32, 920117449#u32), (920117449#u32, 1830196751#u32),
    (1935941148#u32, 1205027416#u32), (1205027416#u32, 211542499#u32),
    (809155383#u32, 303944815#u32), (303944815#u32, 1338328264#u32),
    (541880188#u32, 1280134915#u32), (1280134915#u32, 1605603459#u32),
    (1598024857#u32, 1875094528#u32), (1875094528#u32, 549458790#u32),
    (405858396#u32, 413054922#u32), (413054922#u32, 1741625251#u32),
    (1343434959#u32, 1740046445#u32), (1740046445#u32, 804048688#u32),
    (1697594322#u32, 1318496168#u32), (1318496168#u32, 449889325#u32),
    (1908257733#u32, 904587623#u32), (904587623#u32, 239225914#u32),
    (1569205000#u32, 1460088186#u32), (1460088186#u32, 578278647#u32),
    (742503567#u32, 20511103#u32), (20511103#u32, 1404980080#u32),
    (924436841#u32, 179213100#u32), (179213100#u32, 1223046806#u32),
    (776651208#u32, 1692488596#u32), (1692488596#u32, 1370832439#u32),
    (685109443#u32, 308131929#u32), (308131929#u32, 1462374204#u32),
    (1418607411#u32, 1674242439#u32), (1674242439#u32, 728876236#u32),
    (1831338762#u32, 818744620#u32), (818744620#u32, 316144885#u32),
    (136027637#u32, 84984741#u32), (84984741#u32, 2011456010#u32),
    (832857621#u32, 1800803482#u32), (1800803482#u32, 1314626026#u32),
    (1029184762#u32, 1463990705#u32), (1463990705#u32, 1118298885#u32),
    (1026246497#u32, 462715637#u32), (462715637#u32, 1121237150#u32),
    (1630230719#u32, 432660073#u32), (432660073#u32, 517252928#u32),
    (789199007#u32, 265368403#u32), (265368403#u32, 1358284640#u32),
    (905527003#u32, 2103042246#u32), (2103042246#u32, 1241956644#u32),
    (966963960#u32, 791773240#u32), (791773240#u32, 1180519687#u32),
    (429418708#u32, 1721759118#u32), (1721759118#u32, 1718064939#u32),
    (226919109#u32, 591805476#u32), (591805476#u32, 1920564538#u32),
    (1601482956#u32, 1555011007#u32), (1555011007#u32, 546000691#u32),
    (925678133#u32, 1851895798#u32), (1851895798#u32, 1221805514#u32),
    (890643854#u32, 2061547316#u32), (2061547316#u32, 1256839793#u32),
    (2045776109#u32, 764411913#u32), (764411913#u32, 101707538#u32),
    (142321536#u32, 2005775263#u32), (2005775263#u32, 2005162111#u32),
    (852511271#u32, 383685221#u32), (383685221#u32, 1294972376#u32),
    (1850100142#u32, 606004238#u32), (606004238#u32, 297383505#u32),
    (1988413837#u32, 422428418#u32), (422428418#u32, 159069810#u32),
    (1145573298#u32, 2059018920#u32), (2059018920#u32, 1001910349#u32),
    (1024200565#u32, 2131726269#u32), (2131726269#u32, 1123283082#u32),
    (1335475227#u32, 1076118019#u32), (1076118019#u32, 812008420#u32),
    (430897376#u32, 660937846#u32), (660937846#u32, 1716586271#u32),
    (178995476#u32, 298519990#u32), (298519990#u32, 1968488171#u32),
    (1413092576#u32, 2009537990#u32), (2009537990#u32, 734391071#u32),
    (424922113#u32, 74654605#u32), (74654605#u32, 1722561534#u32),
    (665291814#u32, 184778403#u32), (184778403#u32, 1482191833#u32),
    (90485419#u32, 2034131803#u32), (2034131803#u32, 2056998228#u32),
    (1608154088#u32, 833338502#u32), (833338502#u32, 539329559#u32),
    (473403782#u32, 542036433#u32), (542036433#u32, 1674079865#u32),
    (955512264#u32, 573921543#u32), (573921543#u32, 1191971383#u32),
    (661117737#u32, 832530753#u32), (832530753#u32, 1486365910#u32),
    (251387545#u32, 585003076#u32), (585003076#u32, 1896096102#u32),
    (661565914#u32, 1221956578#u32), (1221956578#u32, 1485917733#u32),
    (420922661#u32, 1190171598#u32), (1190171598#u32, 1726560986#u32),
    (746184711#u32, 1733602777#u32), (1733602777#u32, 1401298936#u32),
    (1717922210#u32, 1653599957#u32), (1653599957#u32, 429561437#u32),
    (742148341#u32, 1117355050#u32), (1117355050#u32, 1405335306#u32),
    (2123635407#u32, 1081507110#u32), (1081507110#u32, 23848240#u32),
    (1274756874#u32, 824918498#u32), (824918498#u32, 872726773#u32),
    (75612694#u32, 638305945#u32), (638305945#u32, 2071870953#u32),
    (1146595981#u32, 37855626#u32), (37855626#u32, 1000887666#u32),
    (1128749075#u32, 1106851245#u32), (1106851245#u32, 1018734572#u32),
    (1189119296#u32, 1858928305#u32), (1858928305#u32, 958364351#u32),
    (1936509027#u32, 329657887#u32), (329657887#u32, 210974620#u32),
    (2067891986#u32, 853385273#u32), (853385273#u32, 79591661#u32),
    (242763393#u32, 80138650#u32), (80138650#u32, 1904720254#u32),
    (202216255#u32, 1166833230#u32), (1166833230#u32, 1945267392#u32),
    (1704605091#u32, 1002003657#u32), (1002003657#u32, 442878556#u32),
    (1228317011#u32, 328390175#u32), (328390175#u32, 919166636#u32),
    (1870718732#u32, 902417887#u32), (902417887#u32, 276764915#u32),
    (1517692234#u32, 1936279112#u32), (1936279112#u32, 629791413#u32),
    (1050410086#u32, 1073301032#u32), (1073301032#u32, 1097073561#u32),
    (558333589#u32, 618725725#u32), (618725725#u32, 1589150058#u32),
    (188438465#u32, 212575099#u32), (212575099#u32, 1959045182#u32),
    (2107512806#u32, 635240816#u32), (635240816#u32, 39970841#u32),
    (1351399750#u32, 1217896196#u32), (1217896196#u32, 796083897#u32),
    (740661540#u32, 1927215114#u32), (1927215114#u32, 1406822107#u32),
    (558100220#u32, 1980501108#u32), (1980501108#u32, 1589383427#u32),
    (2109249359#u32, 247223496#u32), (247223496#u32, 38234288#u32),
    (1012525923#u32, 71691935#u32), (71691935#u32, 1134957724#u32),
    (1828798623#u32, 27117548#u32), (27117548#u32, 318685024#u32),
    (2039959946#u32, 1457037680#u32), (1457037680#u32, 107523701#u32),
    (2038288495#u32, 670227777#u32), (670227777#u32, 109195152#u32),
    (209663158#u32, 168116384#u32), (168116384#u32, 1937820489#u32),
    (984290948#u32, 99941766#u32), (99941766#u32, 1163192699#u32),
    (1252927563#u32, 799345076#u32), (799345076#u32, 894556084#u32),
    (419428947#u32, 1890870518#u32), (1890870518#u32, 1728054700#u32),
    (1157494553#u32, 1817015079#u32), (1817015079#u32, 989989094#u32),
    (891334987#u32, 1040656207#u32), (1040656207#u32, 1256148660#u32),
    (785785922#u32, 1967683322#u32), (1967683322#u32, 1361697725#u32),
    (1302242334#u32, 693913202#u32), (693913202#u32, 845241313#u32),
    (1932511129#u32, 687696804#u32), (687696804#u32, 214972518#u32),
    (429857837#u32, 1376073165#u32), (1376073165#u32, 1717625810#u32),
    (778346524#u32, 2089805548#u32), (2089805548#u32, 1369137123#u32),
    (1132767988#u32, 594038315#u32), (594038315#u32, 1014715659#u32),
    (2078867071#u32, 276497442#u32), (276497442#u32, 68616576#u32),
    (22088804#u32, 47256722#u32), (47256722#u32, 2125394843#u32),
    (2089806413#u32, 155403522#u32), (155403522#u32, 57677234#u32),
    (396887507#u32, 760876211#u32), (760876211#u32, 1750596140#u32),
    (1005915392#u32, 1867478512#u32), (1867478512#u32, 1141568255#u32),
    (1098427204#u32, 880292698#u32), (880292698#u32, 1049056443#u32),
    (10571466#u32, 1530894063#u32), (1530894063#u32, 2136912181#u32),
    (1927076832#u32, 605215390#u32), (605215390#u32, 220406815#u32),
    (1461025413#u32, 1421466600#u32), (1421466600#u32, 686458234#u32),
    (725035983#u32, 816938404#u32), (816938404#u32, 1422447664#u32),
    (381944357#u32, 1303428041#u32), (1303428041#u32, 1765539290#u32),
    (1593271412#u32, 1557280492#u32), (1557280492#u32, 554212235#u32),
    (2095613886#u32, 527857063#u32), (527857063#u32, 51869761#u32),
    (2125667422#u32, 1995711117#u32), (1995711117#u32, 21816225#u32),
    (1589276025#u32, 1583924546#u32), (1583924546#u32, 558207622#u32),
    (425606435#u32, 736395182#u32), (736395182#u32, 1721877212#u32),
    (820025422#u32, 857904003#u32), (857904003#u32, 1327458225#u32),
    (367584259#u32, 2107277889#u32), (2107277889#u32, 1779899388#u32),
    (1845204024#u32, 116979180#u32), (116979180#u32, 302279623#u32),
    (1158837492#u32, 819566845#u32), (819566845#u32, 988646155#u32),
    (1766982315#u32, 596409291#u32), (596409291#u32, 380501332#u32),
    (1060867294#u32, 1016052282#u32), (1016052282#u32, 1086616353#u32),
    (15470579#u32, 1643565293#u32), (1643565293#u32, 2132013068#u32),
    (1886413538#u32, 1618829578#u32), (1618829578#u32, 261070109#u32),
    (1399753701#u32, 1692335411#u32), (1692335411#u32, 747729946#u32),
    (1150072909#u32, 950473072#u32), (950473072#u32, 997410738#u32),
    (894752084#u32, 1749876144#u32), (1749876144#u32, 1252731563#u32),
    (1770167713#u32, 338572024#u32), (338572024#u32, 377315934#u32),
    (1674153723#u32, 1322319557#u32), (1322319557#u32, 473329924#u32),
    (1189130906#u32, 937749255#u32), (937749255#u32, 958352741#u32),
    (406765125#u32, 1121751370#u32), (1121751370#u32, 1740718522#u32),
    (667409179#u32, 1770171037#u32), (1770171037#u32, 1480074468#u32),
    (336549856#u32, 2103544920#u32), (2103544920#u32, 1810933791#u32),
    (1914474864#u32, 440166738#u32), (440166738#u32, 233008783#u32),
    (2003660710#u32, 1164690642#u32), (1164690642#u32, 143822937#u32),
    (440188121#u32, 714460670#u32), (714460670#u32, 1707295526#u32),
    (1894212231#u32, 1899640059#u32), (1899640059#u32, 253271416#u32),
    (1270997537#u32, 1765408850#u32), (1765408850#u32, 876486110#u32),
    (834173210#u32, 2010056637#u32), (2010056637#u32, 1313310437#u32),
    (1080830343#u32, 1196541462#u32), (1196541462#u32, 1066653304#u32),
    (703912353#u32, 1783773358#u32), (1783773358#u32, 1443571294#u32),
    (153621575#u32, 797360221#u32), (797360221#u32, 1993862072#u32),
    (635778846#u32, 1298887220#u32), (1298887220#u32, 1511704801#u32),
    (1420391248#u32, 495658886#u32), (495658886#u32, 727092399#u32),
    (1273099376#u32, 2109025845#u32), (2109025845#u32, 874384271#u32),
    (290670999#u32, 484618707#u32), (484618707#u32, 1856812648#u32),
    (1953093309#u32, 1399852939#u32), (1399852939#u32, 194390338#u32),
    (1931790297#u32, 476503814#u32), (476503814#u32, 215693350#u32),
    (1168611337#u32, 1316554005#u32), (1316554005#u32, 978872310#u32),
    (1318032416#u32, 914753745#u32), (914753745#u32, 829451231#u32),
    (1016770609#u32, 602494260#u32), (602494260#u32, 1130713038#u32),
    (45277316#u32, 1384212302#u32), (1384212302#u32, 2102206331#u32),
    (298013744#u32, 1631477536#u32), (1631477536#u32, 1849469903#u32),
    (1504211713#u32, 91770747#u32), (91770747#u32, 643271934#u32),
    (321646901#u32, 781973549#u32), (781973549#u32, 1825836746#u32),
    (1957773767#u32, 58465136#u32), (58465136#u32, 189709880#u32),
    (838659345#u32, 1494392856#u32), (1494392856#u32, 1308824302#u32),
    (1184172815#u32, 1501800213#u32), (1501800213#u32, 963310832#u32),
    (1421224217#u32, 977701755#u32), (977701755#u32, 726259430#u32),
    (1514835708#u32, 825288080#u32), (825288080#u32, 632647939#u32),
    (963110699#u32, 493845922#u32), (493845922#u32, 1184372948#u32),
    (845600471#u32, 1262183431#u32), (1262183431#u32, 1301883176#u32),
    (779436839#u32, 223436892#u32), (223436892#u32, 1368046808#u32),
    (1371651014#u32, 244997852#u32), (244997852#u32, 775832633#u32),
    (1368395169#u32, 2122900869#u32), (2122900869#u32, 779088478#u32),
    (2039730200#u32, 1811033336#u32), (1811033336#u32, 107753447#u32),
    (162657442#u32, 1560528002#u32), (1560528002#u32, 1984826205#u32),
    (1553098421#u32, 1743803217#u32), (1743803217#u32, 594385226#u32),
    (24486645#u32, 110112918#u32), (110112918#u32, 2122997002#u32),
    (1774553093#u32, 1188070682#u32), (1188070682#u32, 372930554#u32),
    (534092016#u32, 1184883641#u32), (1184883641#u32, 1613391631#u32),
    (1045751413#u32, 627353290#u32), (627353290#u32, 1101732234#u32),
    (903868214#u32, 1028549284#u32), (1028549284#u32, 1243615433#u32),
    (753759022#u32, 1035405166#u32), (1035405166#u32, 1393724625#u32),
    (1952803077#u32, 464954162#u32), (464954162#u32, 194680570#u32),
    (102502428#u32, 487991121#u32), (487991121#u32, 2044981219#u32),
    (286638124#u32, 1789802823#u32), (1789802823#u32, 1860845523#u32),
    (2092563395#u32, 1015929240#u32), (1015929240#u32, 54920252#u32),
    (324159263#u32, 1533483219#u32), (1533483219#u32, 1823324384#u32),
    (804875961#u32, 1759135764#u32), (1759135764#u32, 1342607686#u32),
    (706014569#u32, 1757890570#u32), (1757890570#u32, 1441469078#u32),
    (448402140#u32, 760266418#u32), (760266418#u32, 1699081507#u32),
    (375974868#u32, 1233265083#u32), (1233265083#u32, 1771508779#u32),
    (113762283#u32, 452178713#u32), (452178713#u32, 2033721364#u32),
    (931200852#u32, 642566420#u32), (642566420#u32, 1216282795#u32),
    (1681153485#u32, 1692397259#u32), (1692397259#u32, 466330162#u32),
    (285193818#u32, 765163688#u32), (765163688#u32, 1862289829#u32),
    (394346139#u32, 1629953179#u32), (1629953179#u32, 1753137508#u32),
    (1937755996#u32, 1620967529#u32), (1620967529#u32, 209727651#u32),
    (1742951453#u32, 411462942#u32), (411462942#u32, 404532194#u32),
    (300510473#u32, 181714998#u32), (181714998#u32, 1846973174#u32),
    (379559102#u32, 697727211#u32), (697727211#u32, 1767924545#u32),
    (1556533402#u32, 2005793122#u32), (2005793122#u32, 590950245#u32),
    (1694422100#u32, 342104775#u32), (342104775#u32, 453061547#u32),
    (512321057#u32, 1271549173#u32), (1271549173#u32, 1635162590#u32),
    (1502308947#u32, 1936338240#u32), (1936338240#u32, 645174700#u32),
    (1988815881#u32, 645751943#u32), (645751943#u32, 158667766#u32),
    (675847432#u32, 1010741234#u32), (1010741234#u32, 1471636215#u32),
    (501721213#u32, 24836471#u32), (24836471#u32, 1645762434#u32),
    (1358569314#u32, 679273363#u32), (679273363#u32, 788914333#u32),
    (1484722465#u32, 1078988777#u32), (1078988777#u32, 662761182#u32),
    (277190863#u32, 2137253840#u32), (2137253840#u32, 1870292784#u32),
    (816500702#u32, 1764869715#u32), (1764869715#u32, 1330982945#u32),
    (1259936220#u32, 2067445894#u32), (2067445894#u32, 887547427#u32),
    (1513273850#u32, 1722220683#u32), (1722220683#u32, 634209797#u32),
    (1564688601#u32, 591957108#u32), (591957108#u32, 582795046#u32),
    (1529521733#u32, 1200601350#u32), (1200601350#u32, 617961914#u32),
    (799417018#u32, 157314149#u32), (157314149#u32, 1348066629#u32),
    (1811854824#u32, 734127761#u32), (734127761#u32, 335628823#u32),
    (1312626624#u32, 408174531#u32), (408174531#u32, 834857023#u32),
    (388664435#u32, 1700426073#u32), (1700426073#u32, 1758819212#u32),
    (2129034372#u32, 1920159279#u32), (1920159279#u32, 18449275#u32),
    (1031337775#u32, 1391460640#u32), (1391460640#u32, 1116145872#u32),
    (2083000424#u32, 83400055#u32), (83400055#u32, 64483223#u32),
    (1755212887#u32, 1545248590#u32), (1545248590#u32, 392270760#u32),
    (97731769#u32, 427520892#u32), (427520892#u32, 2049751878#u32),
    (1461518819#u32, 1258709018#u32), (1258709018#u32, 685964828#u32),
    (822026787#u32, 790328297#u32), (790328297#u32, 1325456860#u32),
    (1887931203#u32, 983768063#u32), (983768063#u32, 259552444#u32),
    (1403104042#u32, 1214106139#u32), (1214106139#u32, 744379605#u32),
    (162197904#u32, 1576977305#u32), (1576977305#u32, 1985285743#u32),
    (1519708073#u32, 1761924179#u32), (1761924179#u32, 627775574#u32)
    ]

/-- [aspis_r1_cost_probe::fast_domain::TABLE_B]
    Source: 'crates/aspis-r1-cost-probe/src/fast_domain.rs', lines 144:0-273:2 -/
@[global_simps, irreducible]
def fast_domain.TABLE_B : Array (Std.U32 × Std.U32) 512#usize :=
  Array.make 512#usize [
    (1#u32, 0#u32), (996212859#u32, 1140996376#u32), (2015554631#u32,
    1088093947#u32), (816867225#u32, 1001272228#u32), (1420207432#u32,
    2023238517#u32), (816861480#u32, 962195439#u32), (1720479643#u32,
    177413607#u32), (451378731#u32, 1322552846#u32), (1330239767#u32,
    1446369578#u32), (829529542#u32, 1666749290#u32), (1801405099#u32,
    774845311#u32), (1643336673#u32, 2137148295#u32), (113986326#u32,
    1659849761#u32), (754227675#u32, 49211602#u32), (1719877370#u32,
    1305056920#u32), (124061924#u32, 222841901#u32), (1543902459#u32,
    1632329423#u32), (1497033183#u32, 266384758#u32), (238192698#u32,
    21195821#u32), (1718190259#u32, 219728259#u32), (837291277#u32,
    535367851#u32), (28838794#u32, 517661087#u32), (1008640538#u32,
    1400738499#u32), (18889267#u32, 303036586#u32), (1338697498#u32,
    1881711368#u32), (1486319117#u32, 1051308334#u32), (57413392#u32,
    1672717428#u32), (1698380290#u32, 1660014787#u32), (1128628559#u32,
    487113817#u32), (1021297342#u32, 1410478134#u32), (36983955#u32,
    1951442989#u32), (498386322#u32, 1121034294#u32), (1389168750#u32,
    838891026#u32), (1636834739#u32, 1597012617#u32), (1454515876#u32,
    223346768#u32), (1756352277#u32, 1351837341#u32), (240698073#u32,
    476721530#u32), (427864406#u32, 1584676261#u32), (185070104#u32,
    2052638160#u32), (1275605666#u32, 2095784385#u32), (296310565#u32,
    109983397#u32), (72206514#u32, 1289188236#u32), (709836333#u32,
    1607887694#u32), (1513780754#u32, 2116268837#u32), (472230981#u32,
    1127178204#u32), (337258740#u32, 799789868#u32), (954563443#u32,
    1672118401#u32), (1873486026#u32, 204075296#u32), (13191618#u32,
    303576968#u32), (1514546700#u32, 482975034#u32), (1820378488#u32,
    1427649814#u32), (20135698#u32, 907128133#u32), (1363572456#u32,
    1209117074#u32), (1184836041#u32, 810606909#u32), (483972604#u32,
    51373831#u32), (309323555#u32, 1207665785#u32), (1577483195#u32,
    846841358#u32), (472215603#u32, 885906123#u32), (1804344690#u32,
    999799715#u32), (175617284#u32, 1795732353#u32), (389608651#u32,
    1555639321#u32), (594200728#u32, 1849269846#u32), (329547558#u32,
    1589038929#u32), (2118815938#u32, 2129511119#u32), (438833264#u32,
    1327019128#u32), (1247546638#u32, 2100838754#u32), (287625694#u32,
    714961257#u32), (155805646#u32, 741953977#u32), (694768587#u32,
    1335510377#u32), (414447487#u32, 1660191568#u32), (1684659278#u32,
    1370520300#u32), (467042048#u32, 2131513571#u32), (1384581133#u32,
    347627210#u32), (1780251437#u32, 1948453877#u32), (1421431969#u32,
    974095169#u32), (961627178#u32, 109177970#u32), (1971845238#u32,
    153904061#u32), (1188557366#u32, 413281552#u32), (1923810989#u32,
    1272366406#u32), (2063888815#u32, 129056561#u32), (1635360495#u32,
    1075839836#u32), (330063644#u32, 208626297#u32), (116111969#u32,
    557501350#u32), (1516934575#u32, 1368952111#u32), (2128165408#u32,
    1866558246#u32), (1794178592#u32, 2103779454#u32), (720638041#u32,
    1133563860#u32), (1149377722#u32, 1799983014#u32), (1004021208#u32,
    1870425365#u32), (706427304#u32, 2023867009#u32), (991418403#u32,
    1480232698#u32), (1912203537#u32, 1288850576#u32), (1461783988#u32,
    258760706#u32), (1321308009#u32, 1742025967#u32), (913493534#u32,
    2126309379#u32), (1963867290#u32, 360941673#u32), (377761958#u32,
    572545120#u32), (1665396419#u32, 574316292#u32), (373302001#u32,
    1507699234#u32), (801595255#u32, 1469213224#u32), (2051626085#u32,
    490550043#u32), (996029127#u32, 950036227#u32), (1288641239#u32,
    397886040#u32), (1264385016#u32, 642191549#u32), (324121113#u32,
    147452506#u32), (1953213394#u32, 1643851743#u32), (1002266725#u32,
    1988311862#u32), (991463235#u32, 37546859#u32), (1174950059#u32,
    1819822737#u32), (2040633711#u32, 425180892#u32), (213923363#u32,
    1047884791#u32), (328526853#u32, 975070234#u32), (1825664712#u32,
    501661179#u32), (656109024#u32, 1300585869#u32), (1145588529#u32,
    205357607#u32), (2020371461#u32, 1932572291#u32), (1466126871#u32,
    410615561#u32), (1161400406#u32, 1079422807#u32), (1209061891#u32,
    111843040#u32), (952468088#u32, 412399546#u32), (640220223#u32,
    1154724018#u32), (471738157#u32, 668712505#u32), (1791257284#u32,
    457765379#u32), (317467001#u32, 1766420009#u32), (1581002989#u32,
    970103636#u32), (632980202#u32, 1582071541#u32), (88625828#u32,
    522726826#u32), (914753278#u32, 1399904526#u32), (1799120754#u32,
    343598868#u32), (1039404017#u32, 1538341569#u32), (666420564#u32,
    2135132831#u32), (1006212893#u32, 1489058627#u32), (844712212#u32,
    1454882131#u32), (1438323515#u32, 1182923843#u32), (292417279#u32,
    377436135#u32), (1952780205#u32, 81555357#u32), (521340221#u32,
    1824173925#u32), (1485690416#u32, 559378410#u32), (1714778873#u32,
    1735902582#u32), (1180311432#u32, 639492535#u32), (245650224#u32,
    1174726897#u32), (25525334#u32, 2000505072#u32), (1606261854#u32,
    1606869623#u32), (1061095678#u32, 38145073#u32), (124482577#u32,
    226221110#u32), (172504864#u32, 1916272282#u32), (1564877543#u32,
    99597748#u32), (876115079#u32, 1775942790#u32), (530115096#u32,
    90442098#u32), (1392272834#u32, 993120013#u32), (399207028#u32,
    155898355#u32), (1327578729#u32, 1084731515#u32), (607954189#u32,
    1091734815#u32), (1323669817#u32, 933421634#u32), (1478673705#u32,
    1008068784#u32), (1962335487#u32, 1399131158#u32), (1055871441#u32,
    345775465#u32), (711647904#u32, 1091839298#u32), (881168337#u32,
    157473534#u32), (1723511612#u32, 1949091952#u32), (263253631#u32,
    1948074535#u32), (804296458#u32, 213396278#u32), (153716819#u32,
    2054656334#u32), (2104095544#u32, 1435777142#u32), (1479292912#u32,
    403634516#u32), (565878948#u32, 1786880501#u32), (682480399#u32,
    799350698#u32), (1340472519#u32, 1675598842#u32), (735504938#u32,
    198004457#u32), (848969192#u32, 1414511411#u32), (2083960347#u32,
    2126322313#u32), (1209545065#u32, 1852982367#u32), (386684296#u32,
    1363813538#u32), (1083568418#u32, 725197280#u32), (1439180125#u32,
    915904269#u32), (1480502711#u32, 1450760425#u32), (1488671228#u32,
    939868393#u32), (1982402#u32, 431614399#u32), (1542296538#u32,
    1163978019#u32), (1244152270#u32, 498961107#u32), (1362074261#u32,
    2047718881#u32), (563752921#u32, 1285853654#u32), (1834599352#u32,
    1895440138#u32), (1662799443#u32, 1810348412#u32), (474711937#u32,
    1020011657#u32), (1134947640#u32, 394118266#u32), (1739468984#u32,
    977169647#u32), (227977990#u32, 1816535211#u32), (836848068#u32,
    529120781#u32), (210740911#u32, 1280364462#u32), (581559614#u32,
    117257650#u32), (510094092#u32, 641201894#u32), (503318431#u32,
    730224775#u32), (1571876055#u32, 1388714234#u32), (1320977789#u32,
    1557620475#u32), (118365627#u32, 1759509849#u32), (795729789#u32,
    119644040#u32), (1386331726#u32, 809207732#u32), (753978456#u32,
    488132937#u32), (662367932#u32, 209372338#u32), (940196297#u32,
    1361581394#u32), (550623242#u32, 753832155#u32), (6376089#u32,
    129509954#u32), (446322859#u32, 1580452721#u32), (1755458239#u32,
    1807540371#u32), (2142868905#u32, 574364801#u32), (1596830861#u32,
    2049034655#u32), (1180209648#u32, 441139635#u32), (338018326#u32,
    944583937#u32), (1306248760#u32, 633800785#u32), (2075561284#u32,
    1405804402#u32), (581907879#u32, 73327176#u32), (2049933380#u32,
    1834113202#u32), (1783858788#u32, 875557115#u32), (1718311009#u32,
    1065402188#u32), (1306014716#u32, 1275597287#u32), (1212070390#u32,
    338345678#u32), (1460417120#u32, 797602420#u32), (1852933947#u32,
    203671172#u32), (1545193553#u32, 364584318#u32), (1776630073#u32,
    603111274#u32), (1049445738#u32, 292144592#u32), (954301220#u32,
    1901175687#u32), (923367882#u32, 1744922936#u32), (347749121#u32,
    1576860820#u32), (1986804722#u32, 1373191730#u32), (1616101075#u32,
    811514491#u32), (147800194#u32, 1069151092#u32), (1565145988#u32,
    1765289675#u32), (365445058#u32, 1099441367#u32), (920245660#u32,
    938576836#u32), (204640856#u32, 2040419027#u32), (1213375404#u32,
    771547637#u32), (2064624001#u32, 245417806#u32), (494233883#u32,
    1403803427#u32), (1661270250#u32, 1697085245#u32), (818224288#u32,
    1972399941#u32), (513998937#u32, 202899553#u32), (1757257503#u32,
    734249953#u32), (1601634968#u32, 1790370824#u32), (1829052821#u32,
    673049321#u32), (1765843037#u32, 2085683345#u32), (1213735332#u32,
    1357695652#u32), (1332929929#u32, 2095879383#u32), (914918274#u32,
    1369105915#u32), (1478304746#u32, 406667278#u32), (919065681#u32,
    1216872295#u32), (1932017562#u32, 1757637245#u32), (44588143#u32,
    2058311453#u32), (888152082#u32, 1321895104#u32), (1408222478#u32,
    1721187542#u32), (210392081#u32, 157752587#u32), (1444319707#u32,
    1095294811#u32), (1540140142#u32, 751979754#u32), (570004307#u32,
    1164891669#u32), (1090698404#u32, 2001864991#u32), (595037635#u32,
    2111542451#u32), (433157739#u32, 937025459#u32), (100684459#u32,
    1640456458#u32), (1936161103#u32, 1911011743#u32), (2008329732#u32,
    1737289791#u32), (748970643#u32, 485565246#u32), (1220431105#u32,
    100455014#u32), (1661468032#u32, 1401616134#u32), (798338207#u32,
    2110850421#u32), (1219048271#u32, 773733831#u32), (1789955189#u32,
    505997887#u32), (321157045#u32, 133308492#u32), (1819903752#u32,
    1929668715#u32), (354559414#u32, 1412186133#u32), (683528853#u32,
    193776762#u32), (1371420477#u32, 247094679#u32), (1964662320#u32,
    1382435771#u32), (1249682376#u32, 474254021#u32), (150937652#u32,
    383732090#u32), (588173577#u32, 946133187#u32), (1250840269#u32,
    386418603#u32), (122969455#u32, 311337502#u32), (332209582#u32,
    331411357#u32), (2021756148#u32, 85056840#u32), (1631496031#u32,
    481893475#u32), (964719250#u32, 1012108343#u32), (168460970#u32,
    1615303811#u32), (1764389290#u32, 1617898495#u32), (422755315#u32,
    374503008#u32), (1920015819#u32, 2017323756#u32), (719706205#u32,
    1755223690#u32), (1871020210#u32, 2067959207#u32), (1421883301#u32,
    1767600112#u32), (1742158212#u32, 947474543#u32), (848823435#u32,
    1634673682#u32), (47282233#u32, 1973840192#u32), (1318914216#u32,
    1663922738#u32), (500001204#u32, 1350892375#u32), (2079323762#u32,
    1208852267#u32), (1386607805#u32, 2069854787#u32), (729011542#u32,
    952009042#u32), (1995718635#u32, 990602029#u32), (1079208008#u32,
    2008108071#u32), (985150678#u32, 1044660427#u32), (782570832#u32,
    476532960#u32), (649844810#u32, 475157379#u32), (1462196868#u32,
    1013065725#u32), (405825245#u32, 2000126861#u32), (606906923#u32,
    1264738384#u32), (875583808#u32, 1932435950#u32), (1771477961#u32,
    772209956#u32), (1153435498#u32, 735309441#u32), (291679777#u32,
    1578449442#u32), (1036739736#u32, 4090232#u32), (1954195642#u32,
    800757595#u32), (3045475#u32, 162418948#u32), (953139263#u32,
    265503960#u32), (1255153497#u32, 1873206092#u32), (1109468214#u32,
    24685739#u32), (1194288306#u32, 1664016260#u32), (1954241062#u32,
    1820169310#u32), (461636029#u32, 555407991#u32), (878071934#u32,
    497955134#u32), (1274127696#u32, 398642911#u32), (433600440#u32,
    167145119#u32), (257107986#u32, 1260243949#u32), (2117360294#u32,
    299533990#u32), (1968789303#u32, 1889430098#u32), (18918067#u32,
    521344418#u32), (212412059#u32, 1208547549#u32), (526492512#u32,
    1146089824#u32), (1854906262#u32, 225292938#u32), (2001642678#u32,
    1520422911#u32), (1151864086#u32, 1548621786#u32), (1051514954#u32,
    1945490652#u32), (1231259954#u32, 511844620#u32), (1936661821#u32,
    241049853#u32), (54857805#u32, 2021489568#u32), (2138570352#u32,
    385731389#u32), (830229400#u32, 1396231886#u32), (36975016#u32,
    821963373#u32), (110720662#u32, 731152038#u32), (1672578949#u32,
    179250121#u32), (1682843627#u32, 18309514#u32), (183117139#u32,
    65944434#u32), (1584827345#u32, 909175004#u32), (1845239625#u32,
    562344050#u32), (1315215493#u32, 454778943#u32), (1876139646#u32,
    119923533#u32), (750500769#u32, 1547263668#u32), (849384769#u32,
    61803180#u32), (1513012924#u32, 2142060978#u32), (174156438#u32,
    1448257952#u32), (1976764966#u32, 602953694#u32), (1805314849#u32,
    466904232#u32), (963560469#u32, 803989913#u32), (528497962#u32,
    2048433423#u32), (668998651#u32, 249239603#u32), (58617043#u32,
    693726782#u32), (1475204899#u32, 1648029352#u32), (1576856103#u32,
    1461690978#u32), (1488450015#u32, 601243945#u32), (799756877#u32,
    308500462#u32), (571821609#u32, 1489087773#u32), (1029245122#u32,
    1158447597#u32), (1058730422#u32, 1950344727#u32), (1210158521#u32,
    1506582976#u32), (826608058#u32, 2050139532#u32), (2076036242#u32,
    130048956#u32), (185991083#u32, 1518281638#u32), (1797669071#u32,
    2141355836#u32), (413934600#u32, 1586830163#u32), (845078094#u32,
    149898124#u32), (674296139#u32, 317324829#u32), (25637092#u32,
    421692094#u32), (970891652#u32, 610465777#u32), (647843950#u32,
    788293466#u32), (148228362#u32, 590602766#u32), (69829270#u32,
    1352453515#u32), (1683233817#u32, 1287709593#u32), (887385898#u32,
    608769478#u32), (1269707845#u32, 1452388824#u32), (852276839#u32,
    226974950#u32), (412577235#u32, 1997534047#u32), (1615674956#u32,
    1808914239#u32), (406123904#u32, 764760651#u32), (2126452532#u32,
    708823575#u32), (1991612315#u32, 1875574124#u32), (1475016787#u32,
    1876816901#u32), (1065576003#u32, 1260155159#u32), (150344386#u32,
    103390841#u32), (1736259183#u32, 993645757#u32), (458199028#u32,
    2319221#u32), (870734736#u32, 2085864614#u32), (1388011311#u32,
    312501879#u32), (1669933146#u32, 467772885#u32), (957870942#u32,
    905094216#u32), (1326380755#u32, 140779095#u32), (1569000839#u32,
    48016228#u32), (139466273#u32, 1803083243#u32), (1681738638#u32,
    1038838871#u32), (1677449438#u32, 113082240#u32), (1490057922#u32,
    1016920220#u32), (1801577965#u32, 1312472321#u32), (1214106985#u32,
    780900129#u32), (1907575337#u32, 569832496#u32), (582949328#u32,
    603337063#u32), (2009192190#u32, 566186921#u32), (236415000#u32,
    1220441885#u32), (1100966113#u32, 642444966#u32), (2086832175#u32,
    647027993#u32), (442183737#u32, 184219552#u32), (891287480#u32,
    1172290213#u32), (398898618#u32, 2000607785#u32), (991079294#u32,
    1616314544#u32), (641638338#u32, 1769768123#u32), (1085445012#u32,
    1626464664#u32), (1917457045#u32, 820650395#u32), (1885905244#u32,
    1519283397#u32), (2098046315#u32, 239316783#u32), (1984370174#u32,
    548484416#u32), (1760363481#u32, 2129820178#u32), (1997990904#u32,
    355093967#u32), (1980954341#u32, 561676940#u32), (207319829#u32,
    330698049#u32), (480315830#u32, 137067372#u32), (1608197410#u32,
    953495473#u32), (1433755461#u32, 316564196#u32), (591304555#u32,
    68989614#u32), (569540672#u32, 885330917#u32), (865056590#u32,
    1396323689#u32), (237150930#u32, 715611246#u32), (1167250594#u32,
    1854887903#u32), (112696124#u32, 268389163#u32), (719959488#u32,
    88680757#u32), (498135791#u32, 1918711876#u32), (854984042#u32,
    63484416#u32), (512573355#u32, 559650698#u32), (450129036#u32,
    2130393939#u32), (934129539#u32, 1082077994#u32), (787391422#u32,
    234435571#u32), (808165703#u32, 1317710352#u32), (92769725#u32,
    1231653419#u32), (1699669774#u32, 817702196#u32), (1696657789#u32,
    2121958423#u32), (181669902#u32, 1993442275#u32), (1735177288#u32,
    1041858071#u32), (265914936#u32, 748543764#u32), (2077839401#u32,
    709133143#u32), (479770865#u32, 2027287932#u32), (1742529025#u32,
    278083478#u32), (1334313253#u32, 1249554241#u32), (1124768046#u32,
    299494314#u32), (1055409021#u32, 1215994438#u32), (333636023#u32,
    948573238#u32), (548067276#u32, 713948312#u32), (1458581325#u32,
    1279621404#u32), (1873772561#u32, 1110881047#u32), (994459063#u32,
    1883501554#u32), (308028775#u32, 1118600221#u32), (1924483244#u32,
    1528988896#u32), (176039723#u32, 154417691#u32), (841695573#u32,
    113926739#u32), (52691895#u32, 801280851#u32), (1212320872#u32,
    1495300507#u32), (540487422#u32, 1063443989#u32), (1994468584#u32,
    1611997849#u32), (2119188567#u32, 919124989#u32), (1753543609#u32,
    1294275673#u32), (1908790330#u32, 386453773#u32), (1573749961#u32,
    753946855#u32), (305276529#u32, 1041544704#u32), (128738146#u32,
    457848703#u32), (582395095#u32, 1653762059#u32), (1104635206#u32,
    858881536#u32), (1504303166#u32, 365743328#u32), (122809504#u32,
    181977862#u32), (617875881#u32, 1291144021#u32), (895013455#u32,
    284231781#u32), (1880738855#u32, 621634671#u32), (1300871249#u32,
    1490001285#u32), (454136966#u32, 941654637#u32), (277472845#u32,
    620479805#u32), (594888648#u32, 735387713#u32), (1168068815#u32,
    1631133982#u32), (598225672#u32, 477392696#u32), (1272345615#u32,
    2072662117#u32), (1788571406#u32, 979662875#u32), (655623719#u32,
    353143806#u32), (1258493728#u32, 1482265298#u32), (854296756#u32,
    1657148963#u32), (1287455995#u32, 1262269285#u32), (1389630114#u32,
    73256692#u32), (463066423#u32, 383444756#u32), (401706099#u32,
    967129345#u32), (1055629173#u32, 1510653447#u32), (1775957340#u32,
    1042791219#u32), (1767305484#u32, 1767768510#u32), (702523908#u32,
    198087577#u32), (498379185#u32, 365852161#u32), (1029759507#u32,
    977441374#u32), (531874659#u32, 2093948690#u32), (274337143#u32,
    1881376116#u32), (1734948438#u32, 924408729#u32), (875099799#u32,
    1659345298#u32), (1568619121#u32, 824042977#u32), (936298450#u32,
    1105042578#u32), (1577684276#u32, 2022021752#u32), (404074859#u32,
    398369746#u32), (931704942#u32, 1582955093#u32), (18011247#u32,
    565274326#u32), (931164423#u32, 2037669329#u32), (1309629376#u32,
    2080668066#u32), (1286492231#u32, 1508399759#u32), (1807661853#u32,
    544066780#u32), (1942053500#u32, 1814876063#u32)
    ]

end PRVFresh_C19_F04_AspisR1QueryGeometryActual_Funs_m1
end AspisR1QueryGeometryActual

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F04.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_A : @AspisR1QueryGeometryActual.PRVFresh_C19_F04_AspisR1QueryGeometryActual_Funs_m1.fast_domain.TABLE_A = @AspisR1QueryGeometryActual.fast_domain.TABLE_A := by
  first | (trace "PRV-S1 PRVEq.C19_F04.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_A"; rfl) | (trace "PRV-S2 PRVEq.C19_F04.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_A"; delta AspisR1QueryGeometryActual.PRVFresh_C19_F04_AspisR1QueryGeometryActual_Funs_m1.fast_domain.TABLE_A AspisR1QueryGeometryActual.fast_domain.TABLE_A; try rfl; done)
#print axioms PRVEq.C19_F04.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_A

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F04.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_B : @AspisR1QueryGeometryActual.PRVFresh_C19_F04_AspisR1QueryGeometryActual_Funs_m1.fast_domain.TABLE_B = @AspisR1QueryGeometryActual.fast_domain.TABLE_B := by
  first | (trace "PRV-S1 PRVEq.C19_F04.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_B"; rfl) | (trace "PRV-S2 PRVEq.C19_F04.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_B"; delta AspisR1QueryGeometryActual.PRVFresh_C19_F04_AspisR1QueryGeometryActual_Funs_m1.fast_domain.TABLE_B AspisR1QueryGeometryActual.fast_domain.TABLE_B; try rfl; done)
#print axioms PRVEq.C19_F04.AspisR1QueryGeometryActual.Funs_m1.fast_domain.TABLE_B


end
end PRVBundle_4
section PRVBundle_5
-- GENERATED by PCVH_gen_equalities.py for gate module CurrentCompactCallerModelV1. Statements are against the gate constants of CurrentCompactCallerModelV1.
-- fresh emission: NMP_logical -> PRVFresh_C19_F05_CurrentCompactCallerModelV1_n1; fresh source sha256 a1fcef6b425b598d8c3ce1e52148551e50ced01371871ad9c103837fcd6c090a
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1CurrentCaller
namespace PRVFresh_C19_F05_CurrentCompactCallerModelV1_n1

/-- [aspis_r1_cost_probe::compact::LOGICAL_Y1]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 36:0-36:38
    Visibility: public -/
@[global_simps, irreducible]
def compact.LOGICAL_Y1 : Result Std.Usize := 29#usize * 32#usize

end PRVFresh_C19_F05_CurrentCompactCallerModelV1_n1
end AspisR1CurrentCaller

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F05.CurrentCompactCallerModelV1_n1.compact.LOGICAL_Y1 : @AspisR1CurrentCaller.PRVFresh_C19_F05_CurrentCompactCallerModelV1_n1.compact.LOGICAL_Y1 = @AspisR1CurrentCaller.compact.LOGICAL_Y1 := by
  first | (trace "PRV-S1 PRVEq.C19_F05.CurrentCompactCallerModelV1_n1.compact.LOGICAL_Y1"; rfl) | (trace "PRV-S2 PRVEq.C19_F05.CurrentCompactCallerModelV1_n1.compact.LOGICAL_Y1"; delta AspisR1CurrentCaller.PRVFresh_C19_F05_CurrentCompactCallerModelV1_n1.compact.LOGICAL_Y1 AspisR1CurrentCaller.compact.LOGICAL_Y1; try rfl; done)
#print axioms PRVEq.C19_F05.CurrentCompactCallerModelV1_n1.compact.LOGICAL_Y1


end PRVBundle_5
section PRVBundle_6
-- GENERATED by PCVH_gen_equalities.py for gate module CurrentCompactCallerModelV1. Statements are against the gate constants of CurrentCompactCallerModelV1.
-- fresh emission: NHR_tx2_common -> PRVFresh_C19_F06_CurrentCompactCallerModelV1_n2; fresh source sha256 839e782cd1424221edd0efe35f1e3d1a00e2e7ae7d1336ba84d42ff7b29486f8
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1CurrentCaller
namespace PRVFresh_C19_F06_CurrentCompactCallerModelV1_n2

/-- [aspis_r1_cost_probe::compact::SPLIT]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 27:0-27:28
    Visibility: public -/
@[global_simps, irreducible] def compact.SPLIT : Std.Usize := 10#usize

end PRVFresh_C19_F06_CurrentCompactCallerModelV1_n2
end AspisR1CurrentCaller

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F06.CurrentCompactCallerModelV1_n2.compact.SPLIT : @AspisR1CurrentCaller.PRVFresh_C19_F06_CurrentCompactCallerModelV1_n2.compact.SPLIT = @AspisR1CurrentCaller.compact.SPLIT := by
  first | (trace "PRV-S1 PRVEq.C19_F06.CurrentCompactCallerModelV1_n2.compact.SPLIT"; rfl) | (trace "PRV-S2 PRVEq.C19_F06.CurrentCompactCallerModelV1_n2.compact.SPLIT"; delta AspisR1CurrentCaller.PRVFresh_C19_F06_CurrentCompactCallerModelV1_n2.compact.SPLIT AspisR1CurrentCaller.compact.SPLIT; try rfl; done)
#print axioms PRVEq.C19_F06.CurrentCompactCallerModelV1_n2.compact.SPLIT


end
end PRVBundle_6
section PRVBundle_7
-- GENERATED by PCVH_gen_equalities.py for gate module FinishCandidateExplicitOps. Statements are against the gate constants of FinishCandidateExplicitOps.
-- fresh emission: PCQD_d08a -> PRVFresh_C19_F07_FinishCandidateExplicitOps_n1; fresh source sha256 f449cb3b59b476806a158ef165d9d4e31068ffe7fc88862b819b9055bf0a2a16
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1FinishRelationCurrent
namespace PRVFresh_C19_F07_FinishCandidateExplicitOps_n1

/-- [aspis_r1_cost_probe::transport::{impl core::cmp::PartialEq<aspis_r1_cost_probe::transport::Variant> for aspis_r1_cost_probe::transport::Variant}::eq]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 2:26-2:35
    Visibility: public -/
def transport.Variant.Insts.CoreCmpPartialEqVariant.eq
  (self : transport.Variant) (other : transport.Variant) : Result Bool := do
  let self1 := read_discriminant self
  let other1 := read_discriminant other
  ok (self1 = other1)

/-- [aspis_r1_cost_probe::transport::{aspis_r1_cost_probe::transport::Variant}::folds]:
    Source: 'crates/aspis-r1-cost-probe/src/transport.rs', lines 8:4-8:72
    Visibility: public -/
def transport.Variant.folds (self : transport.Variant) : Result Std.Usize := do
  let b ←
    transport.Variant.Insts.CoreCmpPartialEqVariant.eq self
      transport.Variant.S1
  if b
  then ok 1#usize
  else ok 2#usize

end PRVFresh_C19_F07_FinishCandidateExplicitOps_n1
end AspisR1FinishRelationCurrent

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F07.FinishCandidateExplicitOps_n1.transport.Variant.Insts.CoreCmpPartialEqVariant.eq : @AspisR1FinishRelationCurrent.PRVFresh_C19_F07_FinishCandidateExplicitOps_n1.transport.Variant.Insts.CoreCmpPartialEqVariant.eq = @AspisR1FinishRelationCurrent.transport.Variant.Insts.CoreCmpPartialEqVariant.eq := by
  first | (trace "PRV-S1 PRVEq.C19_F07.FinishCandidateExplicitOps_n1.transport.Variant.Insts.CoreCmpPartialEqVariant.eq"; rfl) | (trace "PRV-S2 PRVEq.C19_F07.FinishCandidateExplicitOps_n1.transport.Variant.Insts.CoreCmpPartialEqVariant.eq"; delta AspisR1FinishRelationCurrent.PRVFresh_C19_F07_FinishCandidateExplicitOps_n1.transport.Variant.Insts.CoreCmpPartialEqVariant.eq AspisR1FinishRelationCurrent.transport.Variant.Insts.CoreCmpPartialEqVariant.eq; try rfl; done)
#print axioms PRVEq.C19_F07.FinishCandidateExplicitOps_n1.transport.Variant.Insts.CoreCmpPartialEqVariant.eq

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F07.FinishCandidateExplicitOps_n1.transport.Variant.folds : @AspisR1FinishRelationCurrent.PRVFresh_C19_F07_FinishCandidateExplicitOps_n1.transport.Variant.folds = @AspisR1FinishRelationCurrent.transport.Variant.folds := by
  first | (trace "PRV-S1 PRVEq.C19_F07.FinishCandidateExplicitOps_n1.transport.Variant.folds"; rfl) | (trace "PRV-S2 PRVEq.C19_F07.FinishCandidateExplicitOps_n1.transport.Variant.folds"; delta AspisR1FinishRelationCurrent.PRVFresh_C19_F07_FinishCandidateExplicitOps_n1.transport.Variant.folds AspisR1FinishRelationCurrent.transport.Variant.folds; try simp only [PRVEq.C19_F07.FinishCandidateExplicitOps_n1.transport.Variant.Insts.CoreCmpPartialEqVariant.eq]; try rfl; done)
#print axioms PRVEq.C19_F07.FinishCandidateExplicitOps_n1.transport.Variant.folds


end PRVBundle_7
section PRVBundle_8
-- GENERATED by PCQI_gen_equalities.py for gate module R1CandidateWideParserSource. Statements are against the gate constants of R1CandidateWideParserSource.
-- fresh emission: NMH_wide_decode -> PRVFresh_C19_F08_R1CandidateWideParserSource_j1; fresh source sha256 8a77c6278b0643da5b0fae48f1923133135d20d404d78da0a290caf0544ab2a3
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1CandidateParser
namespace PRVFresh_C19_F08_R1CandidateWideParserSource_j1

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::BYTE_LEN]
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 35:4-35:35
    Visibility: public -/
@[global_simps, irreducible]
def field.wide_exact.WideExact.BYTE_LEN : Std.Usize := 32#usize

/-- [aspis_core::field::P]
    Source: 'crates/aspis-core/src/field.rs', lines 19:0-19:31
    Visibility: public -/
@[global_simps, irreducible] def field.P : Std.U32 := 2147483647#u32

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_limbs]:
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 207:4-235:5
    Visibility: public -/
def field.wide_exact.WideExact.from_limbs
  (limbs : Array Std.U32 8#usize) :
  Result (Option field.wide_exact.WideExact)
  := do
  let i ← Array.index_usize limbs 0#usize
  if i >= field.P
  then ok none
  else
    let i1 ← Array.index_usize limbs 1#usize
    if i1 >= field.P
    then ok none
    else
      let i2 ← Array.index_usize limbs 2#usize
      if i2 >= field.P
      then ok none
      else
        let i3 ← Array.index_usize limbs 3#usize
        if i3 >= field.P
        then ok none
        else
          let i4 ← Array.index_usize limbs 4#usize
          if i4 >= field.P
          then ok none
          else
            let i5 ← Array.index_usize limbs 5#usize
            if i5 >= field.P
            then ok none
            else
              let i6 ← Array.index_usize limbs 6#usize
              if i6 >= field.P
              then ok none
              else
                let i7 ← Array.index_usize limbs 7#usize
                if i7 >= field.P
                then ok none
                else
                  ok (some
                    {
                      c0 :=
                        { c0 := { a := i, b := i1 }, c1 := { a := i2, b := i3 }
                        },
                      c1 :=
                        {
                          c0 := { a := i4, b := i5 },
                          c1 := { a := i6, b := i7 }
                        }
                    })

/-- [aspis_core::field::wide_exact::{aspis_core::field::wide_exact::WideExact}::from_le_bytes]:
    Source: 'crates/aspis-core/src/field/wide_exact.rs', lines 255:4-270:5
    Visibility: public -/
def field.wide_exact.WideExact.from_le_bytes
  (bytes : Slice Std.U8) : Result (Option field.wide_exact.WideExact) := do
  let i := Slice.len bytes
  if i != field.wide_exact.WideExact.BYTE_LEN
  then ok none
  else
    let i1 ← Slice.index_usize bytes 0#usize
    let i2 ← Slice.index_usize bytes 1#usize
    let i3 ← Slice.index_usize bytes 2#usize
    let i4 ← Slice.index_usize bytes 3#usize
    let i5 ←
      lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i1, i2, i3, i4 ]))
    let i6 ← Slice.index_usize bytes 4#usize
    let i7 ← Slice.index_usize bytes 5#usize
    let i8 ← Slice.index_usize bytes 6#usize
    let i9 ← Slice.index_usize bytes 7#usize
    let i10 ←
      lift (core.num.U32.from_le_bytes (Array.make 4#usize [ i6, i7, i8, i9 ]))
    let i11 ← Slice.index_usize bytes 8#usize
    let i12 ← Slice.index_usize bytes 9#usize
    let i13 ← Slice.index_usize bytes 10#usize
    let i14 ← Slice.index_usize bytes 11#usize
    let i15 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i11, i12, i13, i14 ]))
    let i16 ← Slice.index_usize bytes 12#usize
    let i17 ← Slice.index_usize bytes 13#usize
    let i18 ← Slice.index_usize bytes 14#usize
    let i19 ← Slice.index_usize bytes 15#usize
    let i20 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i16, i17, i18, i19 ]))
    let i21 ← Slice.index_usize bytes 16#usize
    let i22 ← Slice.index_usize bytes 17#usize
    let i23 ← Slice.index_usize bytes 18#usize
    let i24 ← Slice.index_usize bytes 19#usize
    let i25 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i21, i22, i23, i24 ]))
    let i26 ← Slice.index_usize bytes 20#usize
    let i27 ← Slice.index_usize bytes 21#usize
    let i28 ← Slice.index_usize bytes 22#usize
    let i29 ← Slice.index_usize bytes 23#usize
    let i30 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i26, i27, i28, i29 ]))
    let i31 ← Slice.index_usize bytes 24#usize
    let i32 ← Slice.index_usize bytes 25#usize
    let i33 ← Slice.index_usize bytes 26#usize
    let i34 ← Slice.index_usize bytes 27#usize
    let i35 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i31, i32, i33, i34 ]))
    let i36 ← Slice.index_usize bytes 28#usize
    let i37 ← Slice.index_usize bytes 29#usize
    let i38 ← Slice.index_usize bytes 30#usize
    let i39 ← Slice.index_usize bytes 31#usize
    let i40 ←
      lift (core.num.U32.from_le_bytes
        (Array.make 4#usize [ i36, i37, i38, i39 ]))
    field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [ i5, i10, i15, i20, i25, i30, i35, i40 ])

end PRVFresh_C19_F08_R1CandidateWideParserSource_j1
end AspisR1CandidateParser


open Aeneas Aeneas.Std Result ControlFlow Error
namespace PCVH
open AspisR1CandidateParser

abbrev W := field.wide_exact.WideExact

def lm (a b c d : Std.U8) : Std.U32 := core.num.U32.from_le_bytes (Array.make 4#usize [a, b, c, d])

def dec_cm (x y : Std.U32) : Option field.CM31 :=
  if x >= field.P then none else if y >= field.P then none else some { a := x, b := y }
def dec_qm (c d : Option field.CM31) : Option field.QM31 :=
  match c with | none => none | some c => match d with | none => none | some d => some { c0 := c, c1 := d }
def dec_w (c d : Option field.QM31) : Option W :=
  match c with | none => none | some c => match d with | none => none | some d => some { c0 := c, c1 := d }

theorem fr_none (T : Type) : core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual T none = ok none := by
  simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual, massert, optionTag, read_discriminant]

theorem cm31_eq (b0 b1 b2 b3 b4 b5 b6 b7 : Std.U8) (h : [b0, b1, b2, b3, b4, b5, b6, b7].length ≤ Usize.max) :
    field.CM31.from_le_bytes ⟨[b0, b1, b2, b3, b4, b5, b6, b7], h⟩ = ok (dec_cm (lm b0 b1 b2 b3) (lm b4 b5 b6 b7)) := by
  simp [field.CM31.from_le_bytes, field.M31.from_le_bytes, Aeneas.Std.lift, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from, dec_cm, lm, Array.make]
  split <;> (try split) <;> simp_all [fr_none]

theorem qm31_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Std.U8) (h : [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15].length ≤ Usize.max) :
    field.QM31.from_le_bytes ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15], h⟩ =
      ok (dec_qm (dec_cm (lm b0 b1 b2 b3) (lm b4 b5 b6 b7)) (dec_cm (lm b8 b9 b10 b11) (lm b12 b13 b14 b15))) := by
  simp [field.QM31.from_le_bytes, Aeneas.Std.lift, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from, cm31_eq, dec_qm]
  generalize dec_cm (lm b0 b1 b2 b3) (lm b4 b5 b6 b7) = c
  generalize dec_cm (lm b8 b9 b10 b11) (lm b12 b13 b14 b15) = d
  cases c <;> cases d <;> simp [fr_none]

theorem wide_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : Std.U8) (h : [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31].length ≤ Usize.max) :
    field.wide_exact.WideExact.from_le_bytes ⟨[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], h⟩ =
      ok (dec_w (dec_qm (dec_cm (lm b0 b1 b2 b3) (lm b4 b5 b6 b7)) (dec_cm (lm b8 b9 b10 b11) (lm b12 b13 b14 b15)))
                (dec_qm (dec_cm (lm b16 b17 b18 b19) (lm b20 b21 b22 b23)) (dec_cm (lm b24 b25 b26 b27) (lm b28 b29 b30 b31)))) := by
  simp [field.wide_exact.WideExact.from_le_bytes, field.wide_exact.WideExact.BYTE_LEN, Slice.len, Aeneas.Std.lift, core.option.Option.Insts.CoreOpsTry_traitTry.branch, core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice.index, core.array.TryFromArrayCopySlice.try_from, qm31_eq, dec_w]
  generalize dec_qm (dec_cm (lm b0 b1 b2 b3) (lm b4 b5 b6 b7)) (dec_cm (lm b8 b9 b10 b11) (lm b12 b13 b14 b15)) = c
  generalize dec_qm (dec_cm (lm b16 b17 b18 b19) (lm b20 b21 b22 b23)) (dec_cm (lm b24 b25 b26 b27) (lm b28 b29 b30 b31)) = d
  cases c <;> cases d <;> simp [fr_none]

theorem chain (x0 x1 x2 x3 x4 x5 x6 x7 : Std.U32) :
    (ok (dec_w (dec_qm (dec_cm x0 x1) (dec_cm x2 x3)) (dec_qm (dec_cm x4 x5) (dec_cm x6 x7))) : Result (Option W)) =
    (if x0 >= field.P then ok none else if x1 >= field.P then ok none else if x2 >= field.P then ok none else if x3 >= field.P then ok none else if x4 >= field.P then ok none else if x5 >= field.P then ok none else if x6 >= field.P then ok none else if x7 >= field.P then ok none else ok (some { c0 := { c0 := { a := x0, b := x1 }, c1 := { a := x2, b := x3 } }, c1 := { c0 := { a := x4, b := x5 }, c1 := { a := x6, b := x7 } } }) : Result (Option W)) := by
  by_cases h0 : x0 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0]
  by_cases h1 : x1 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1]
  by_cases h2 : x2 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2]
  by_cases h3 : x3 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3]
  by_cases h4 : x4 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4]
  by_cases h5 : x5 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4, h5]
  by_cases h6 : x6 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4, h5, h6]
  by_cases h7 : x7 >= field.P
  · simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4, h5, h6, h7]
  simp [dec_w, dec_qm, dec_cm, h0, h1, h2, h3, h4, h5, h6, h7]

theorem main :
    @AspisR1CandidateParser.PRVFresh_C19_F08_R1CandidateWideParserSource_j1.field.wide_exact.WideExact.from_le_bytes =
    @AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes := by
  funext bytes
  obtain ⟨l, hl⟩ := bytes
  by_cases h : l.length = 32
  · rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23, _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | ⟨b32, tl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> first | (exfalso; simp at h; done) | skip
    all_goals
      rw [wide_eq b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 hl, chain]
      with_unfolding_all rfl
  · unfold AspisR1CandidateParser.PRVFresh_C19_F08_R1CandidateWideParserSource_j1.field.wide_exact.WideExact.from_le_bytes AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
    simp [Slice.len, AspisR1CandidateParser.PRVFresh_C19_F08_R1CandidateWideParserSource_j1.field.wide_exact.WideExact.BYTE_LEN, AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN, h]
end PCVH

theorem PRVEq.C19_F08.R1CandidateWideParserSource_k1.field.wide_exact.WideExact.from_le_bytes :
    @AspisR1CandidateParser.PRVFresh_C19_F08_R1CandidateWideParserSource_j1.field.wide_exact.WideExact.from_le_bytes =
    @AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes := PCVH.main
#print axioms PRVEq.C19_F08.R1CandidateWideParserSource_k1.field.wide_exact.WideExact.from_le_bytes

end PRVBundle_8
section PRVBundle_9
-- GENERATED by PCVH_gen_equalities.py for gate module Stage2ContinuationTypes. Statements are against the gate constants of Stage2ContinuationTypes.
-- fresh emission: PCQD_d11b -> PRVFresh_C19_F09_Stage2ContinuationTypes_n2; fresh source sha256 e177b29f7bed8c55ddaef518f2c7a303316a00b6af16a4c3fcefc16e5cdf782d
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

namespace AspisR1Stage2
namespace PRVFresh_C19_F09_Stage2ContinuationTypes_n2

/-- [aspis_core::field::M31]
    Source: 'crates/aspis-core/src/field.rs', lines 23:0-23:14
    Name pattern: [aspis_core::field::M31]
    Visibility: public -/
@[reducible]
def aspis_core.field.M31 := Std.U32

/-- [aspis_core::field::CM31]
    Source: 'crates/aspis-core/src/field.rs', lines 255:0-255:15
    Name pattern: [aspis_core::field::CM31]
    Visibility: public -/
structure aspis_core.field.CM31 where
  a : aspis_core.field.M31
  b : aspis_core.field.M31

/-- [aspis_core::field::QM31]
    Source: 'crates/aspis-core/src/field.rs', lines 432:0-432:15
    Name pattern: [aspis_core::field::QM31]
    Visibility: public -/
structure aspis_core.field.QM31 where
  c0 : aspis_core.field.CM31
  c1 : aspis_core.field.CM31

/-- [aspis_r1_cost_probe::verifier::Error]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 20:0-27:38
    Visibility: public -/
inductive verifier.Error where
| Parse : verifier.Error
| Semantic : verifier.Error
| Transcript : verifier.Error
| Relation : verifier.Error
| Merkle : verifier.Error
| Query : verifier.Error
| Checkpoint : verifier.Error
| Allocation : verifier.Error

/-- [aspis_r1_cost_probe::verifier::Reader]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 342:0-342:41 -/
structure verifier.Reader where
  bytes : Slice Std.U8
  «at» : Std.Usize

end PRVFresh_C19_F09_Stage2ContinuationTypes_n2
end AspisR1Stage2

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.M31 : @AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.aspis_core.field.M31 = @AspisR1Stage2.aspis_core.field.M31 := by
  first | (trace "PRV-S1 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.M31"; rfl) | (trace "PRV-S2 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.M31"; delta AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.aspis_core.field.M31 AspisR1Stage2.aspis_core.field.M31; try rfl; done)
#print axioms PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.M31

set_option maxHeartbeats 200000 in
def PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31.equiv : AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.aspis_core.field.CM31 ≃ AspisR1Stage2.aspis_core.field.CM31 where
  toFun x := { a := x.a, b := x.b }
  invFun y := { a := y.a, b := y.b }
  left_inv x := by
    first | (trace "PRV-S1 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31"; cases x; rfl) | (trace "PRV-S2 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31"; cases x; simp)
  right_inv y := by
    first | (trace "PRV-S1 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31"; cases y; rfl) | (trace "PRV-S2 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31"; cases y; simp)
#print axioms PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.QM31.equiv : AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.aspis_core.field.QM31 ≃ AspisR1Stage2.aspis_core.field.QM31 where
  toFun x := { c0 := (PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31.equiv x.c0), c1 := (PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31.equiv x.c1) }
  invFun y := { c0 := (PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31.equiv.symm y.c0), c1 := (PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.CM31.equiv.symm y.c1) }
  left_inv x := by
    first | (trace "PRV-S1 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.QM31"; cases x; rfl) | (trace "PRV-S2 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.QM31"; cases x; simp)
  right_inv y := by
    first | (trace "PRV-S1 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.QM31"; cases y; rfl) | (trace "PRV-S2 PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.QM31"; cases y; simp)
#print axioms PRVEq.C19_F09.Stage2ContinuationTypes_n2.aspis_core.field.QM31.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Error.equiv : AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error ≃ AspisR1Stage2.verifier.Error where
  toFun x := match x with
    | AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Parse => AspisR1Stage2.verifier.Error.Parse 
    | AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Semantic => AspisR1Stage2.verifier.Error.Semantic 
    | AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Transcript => AspisR1Stage2.verifier.Error.Transcript 
    | AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Relation => AspisR1Stage2.verifier.Error.Relation 
    | AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Merkle => AspisR1Stage2.verifier.Error.Merkle 
    | AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Query => AspisR1Stage2.verifier.Error.Query 
    | AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Checkpoint => AspisR1Stage2.verifier.Error.Checkpoint 
    | AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Allocation => AspisR1Stage2.verifier.Error.Allocation 
  invFun y := match y with
    | AspisR1Stage2.verifier.Error.Parse => AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Parse 
    | AspisR1Stage2.verifier.Error.Semantic => AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Semantic 
    | AspisR1Stage2.verifier.Error.Transcript => AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Transcript 
    | AspisR1Stage2.verifier.Error.Relation => AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Relation 
    | AspisR1Stage2.verifier.Error.Merkle => AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Merkle 
    | AspisR1Stage2.verifier.Error.Query => AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Query 
    | AspisR1Stage2.verifier.Error.Checkpoint => AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Checkpoint 
    | AspisR1Stage2.verifier.Error.Allocation => AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Error.Allocation 
  left_inv x := by
    (trace "PRV-S1 PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Error"; cases x <;> rfl)
  right_inv y := by
    (trace "PRV-S1 PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Error"; cases y <;> rfl)
#print axioms PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Error.equiv

set_option maxHeartbeats 200000 in
def PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Reader.equiv : AspisR1Stage2.PRVFresh_C19_F09_Stage2ContinuationTypes_n2.verifier.Reader ≃ AspisR1Stage2.verifier.Reader where
  toFun x := { bytes := x.bytes, «at» := x.«at» }
  invFun y := { bytes := y.bytes, «at» := y.«at» }
  left_inv x := by
    first | (trace "PRV-S1 PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Reader"; cases x; rfl) | (trace "PRV-S2 PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Reader"; cases x; simp)
  right_inv y := by
    first | (trace "PRV-S1 PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Reader"; cases y; rfl) | (trace "PRV-S2 PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Reader"; cases y; simp)
#print axioms PRVEq.C19_F09.Stage2ContinuationTypes_n2.verifier.Reader.equiv


end PRVBundle_9
section PRVBundle_10
-- PCVI_ item 3: NMT stage1_owned (second shape, order table). Fresh text: model-bridge-20261111/NND_reuse/NMT_fresh/.../stage1_owned/raw/NMT_stage1_owned/Funs.lean
-- (Aeneas emission of programs/r1-cost-probe, r1_pool_adapter_owned.rs). Each external callee is replaced by the gate's NMT_call_k parameter
-- in the order read off the gate body: 0 Slice ne, 1 Slice eq, 2 Result.map_err, 3 Variant.tag, 4 PROOF_BYTES, 5 semantic_public, 6 common,
-- 7 validate_..._statement_v1, 8 POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES, 9 encode_..._afterstate_v1, 10 ProgramError clone, 11 first_decoded,
-- 12 decode_public_statement_box, 13 require_readonly_buffer, 14 require_verifier_checkpoint, 15 require_distinct_accounts, 16 require_zero.
-- Statement quantifies over all callees; which frozen items they are is the binding at the instantiation (CONDITIONAL_ON_BINDING).
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace NMT_stage1_owned
namespace PRVFresh_C19_F10_i1
-- Opaque callees are explicit parameters, never axioms.
variable (NMT_call_0 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U),
(Slice T) → (Array U N) → Result Bool)

variable (NMT_call_1 : ∀ {T : Type} {U : Type} {N : Std.Usize} (cmpPartialEqInst : core.cmp.PartialEq
  T U),
(Slice T) → (Array U N) → Result Bool)

variable (NMT_call_2 : ∀ {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
  core.ops.function.FnOnce O E F),
(core.result.Result T E) → O → Result (core.result.Result T F))

variable (NMT_call_3 : aspis_r1_cost_probe.transport.Variant → Result Std.U8)

variable (NMT_call_4 : Result Std.Usize)

variable (NMT_call_5 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)

variable (NMT_call_6 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1)

variable (NMT_call_7 : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    → Result (core.result.Result Unit
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1))

variable (NMT_call_8 : Result Std.Usize)

variable (NMT_call_9 : aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 →
    Result (core.result.Result (Array Std.U8 688#usize)
    aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1))

variable (NMT_call_10 : solana_program_error.ProgramError → Result
    solana_program_error.ProgramError)

variable (NMT_call_11 : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Slice
    Std.U8) → (Slice Std.U8) → Std.Usize → Result (core.result.Result
    (alloc.vec.Vec Std.U8) solana_program_error.ProgramError))

variable (NMT_call_12 : (Slice Std.U8) → Result (core.result.Result
    aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1
    solana_program_error.ProgramError))

variable (NMT_call_13 : r1_pool_adapter.owned.OwnedAccount → Result (core.result.Result Unit
    solana_program_error.ProgramError))

variable (NMT_call_14 : r1_pool_adapter.owned.OwnedAccount → solana_pubkey.Pubkey → Bool →
    Result (core.result.Result Unit solana_program_error.ProgramError))

variable (NMT_call_15 : ∀ {N : Std.Usize},
(Array r1_pool_adapter.owned.OwnedAccount N) → Result (core.result.Result
    Unit solana_program_error.ProgramError))

variable (NMT_call_16 : (Slice Std.U8) → Result (core.result.Result Unit
    solana_program_error.ProgramError))

/-- OwnedAccount.data with the SDK clone callee as the parameter NMT_call_10 (as in the gate). -/
def r1_pool_adapter.owned.OwnedAccount.data (NMT_call_10 : solana_program_error.ProgramError → Result
    solana_program_error.ProgramError)
  (self : r1_pool_adapter.owned.OwnedAccount) :
  Result (core.result.Result (Slice Std.U8) solana_program_error.ProgramError)
  := do
  match self.bytes with
  | core.result.Result.Ok bytes =>
    let s := alloc.vec.Vec.deref bytes
    ok (core.result.Result.Ok s)
  | core.result.Result.Err error =>
    let pe ← NMT_call_10 error
    ok (core.result.Result.Err pe)

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1,), solana_program_error::ProgramError> for aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::closure#1}::call_once]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 396:13-396:49 -/
def
  r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
  (c : r1_pool_adapter.owned.stage1_owned.closure_1)
  (tupled_args :
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1) :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

/-- Trait implementation: [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1,), solana_program_error::ProgramError> for aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::closure#1}]
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 396:13-396:49 -/
@[reducible]
def
  r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.owned.stage1_owned.closure_1
  aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifierTransportErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError.call_once
}

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1,), solana_program_error::ProgramError> for aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::closure}::call_once]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 392:17-392:53 -/
def
  r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
  (c : r1_pool_adapter.owned.stage1_owned.closure)
  (tupled_args :
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  :
  Result solana_program_error.ProgramError
  := do
  ok solana_program_error.ProgramError.InvalidAccountData

/-- Trait implementation: [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::{impl core::ops::function::FnOnce<(aspis_statement::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1,), solana_program_error::ProgramError> for aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned::closure}]
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 392:17-392:53 -/
@[reducible]
def
  r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
  : core.ops.function.FnOnce r1_pool_adapter.owned.stage1_owned.closure
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
  solana_program_error.ProgramError := {
  call_once :=
    r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError.call_once
}

/-- [aspis_r1_cost_probe_program::r1_pool_adapter::owned::stage1_owned]:
    Source: 'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs', lines 376:0-414:1 -/
def r1_pool_adapter.owned.stage1_owned
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8) :
  Result (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let b ←
    NMT_call_1 core.cmp.PartialEqU8 data
      (Array.make 2#usize [ 3#u8, 10#u8 ])
  if b
  then
    let i := Slice.len accounts
    if i != 3#usize
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let proof_account ← Slice.index_usize accounts 0#usize
      let public_account ← Slice.index_usize accounts 1#usize
      let checkpoint_account ← Slice.index_usize accounts 2#usize
      let r ←
        NMT_call_15
          (Array.make 3#usize [
            proof_account, public_account, checkpoint_account
            ])
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r1 ← NMT_call_13 proof_account
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r2 ←
            NMT_call_13 public_account
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r3 ←
              NMT_call_14
                checkpoint_account program_id true
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r4 ←
                (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10) checkpoint_account
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r5 ← NMT_call_16 val
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let r6 ←
                    (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10) public_account
                  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                  match cf6 with
                  | core.ops.control_flow.ControlFlow.Continue val1 =>
                    let r7 ← NMT_call_12 val1
                    let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf7 with
                    | core.ops.control_flow.ControlFlow.Continue val2 =>
                      let r8 ←
                        NMT_call_7
                          val2
                      let r9 ←
                        NMT_call_2
                          r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                          r8 ()
                      let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r9
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let pvpftcv ←
                          NMT_call_6
                            val2
                        let r10 ←
                          NMT_call_9
                            pvpftcv.lane_transition.candidate_afterstate
                        let r11 ←
                          NMT_call_2
                            r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                            r10 ()
                        let cf9 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val3 =>
                          let r12 ←
                            (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10)
                              proof_account
                          let cf10 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val4 =>
                            let proof_length ←
                              NMT_call_4
                            let proof_start ←
                              NMT_call_8
                            let o ←
                              lift (Usize.checked_add proof_start proof_length)
                            let r13 ←
                              core.option.Option.ok_or o
                                solana_program_error.ProgramError.InvalidAccountData
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val5
                              =>
                              let i1 := Slice.len val4
                              if i1 != val5
                              then
                                ok (core.result.Result.Err
                                  solana_program_error.ProgramError.InvalidAccountData)
                              else
                                let s ←
                                  core.slice.index.Slice.index
                                    (core.slice.index.SliceIndexRangeToUsizeSlice
                                    Std.U8) val4 { «end» := proof_start }
                                let b1 ←
                                  NMT_call_0
                                    core.cmp.PartialEqU8 s val3
                                if b1
                                then
                                  ok (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let i2 ←
                                    lift (Std.Usize.wrapping_add proof_start
                                      8#usize)
                                  let i3 ← Slice.index_usize val4 i2
                                  let i4 ←
                                    NMT_call_3
                                      aspis_r1_cost_probe.transport.Variant.S2
                                  if i3 != i4
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let p ←
                                      NMT_call_5
                                        val2
                                    let s1 ←
                                      core.slice.index.Slice.index
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                        Std.U8) val4
                                        { start := proof_start, «end» := val5
                                        }
                                    let i5 ← Slice.index_usize data 1#usize
                                    let i6 ← lift (UScalar.cast .Usize i5)
                                    let r14 ← NMT_call_11 p val1 s1 i6
                                    let cf12 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r14
                                    match cf12 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val6 =>
                                      let i7 := alloc.vec.Vec.len val6
                                      let i8 := Slice.len val
                                      if i7 != i8
                                      then
                                        ok (core.result.Result.Err
                                          solana_program_error.ProgramError.InvalidAccountData)
                                      else ok (core.result.Result.Ok val6)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (alloc.vec.Vec Std.U8)
                                        (core.convert.FromSame
                                        solana_program_error.ProgramError)
                                        residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame
          solana_program_error.ProgramError) residual
  else
    let b1 ←
      NMT_call_1 core.cmp.PartialEqU8 data
        (Array.make 2#usize [ 3#u8, 11#u8 ])
    if b1
    then
      let i := Slice.len accounts
      if i != 3#usize
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData)
      else
        let proof_account ← Slice.index_usize accounts 0#usize
        let public_account ← Slice.index_usize accounts 1#usize
        let checkpoint_account ← Slice.index_usize accounts 2#usize
        let r ←
          NMT_call_15
            (Array.make 3#usize [
              proof_account, public_account, checkpoint_account
              ])
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r1 ←
            NMT_call_13 proof_account
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r2 ←
              NMT_call_13 public_account
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r3 ←
                NMT_call_14
                  checkpoint_account program_id true
              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r4 ←
                  (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10) checkpoint_account
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let r5 ← NMT_call_16 val
                  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let r6 ←
                      (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10) public_account
                    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue val1 =>
                      let r7 ←
                        NMT_call_12 val1
                      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue val2 =>
                        let r8 ←
                          NMT_call_7
                            val2
                        let r9 ←
                          NMT_call_2
                            r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                            r8 ()
                        let cf8 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let pvpftcv ←
                            NMT_call_6
                              val2
                          let r10 ←
                            NMT_call_9
                              pvpftcv.lane_transition.candidate_afterstate
                          let r11 ←
                            NMT_call_2
                              r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                              r10 ()
                          let cf9 ←
                            core.result.Result.Insts.CoreOpsTry.branch r11
                          match cf9 with
                          | core.ops.control_flow.ControlFlow.Continue val3 =>
                            let r12 ←
                              (r1_pool_adapter.owned.OwnedAccount.data NMT_call_10)
                                proof_account
                            let cf10 ←
                              core.result.Result.Insts.CoreOpsTry.branch r12
                            match cf10 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let proof_length ←
                                NMT_call_4
                              let proof_start ←
                                NMT_call_8
                              let o ←
                                lift (Usize.checked_add proof_start
                                  proof_length)
                              let r13 ←
                                core.option.Option.ok_or o
                                  solana_program_error.ProgramError.InvalidAccountData
                              let cf11 ←
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              match cf11 with
                              | core.ops.control_flow.ControlFlow.Continue val5
                                =>
                                let i1 := Slice.len val4
                                if i1 != val5
                                then
                                  ok (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let s ←
                                    core.slice.index.Slice.index
                                      (core.slice.index.SliceIndexRangeToUsizeSlice
                                      Std.U8) val4 { «end» := proof_start }
                                  let b2 ←
                                    NMT_call_0
                                      core.cmp.PartialEqU8 s val3
                                  if b2
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let i2 ←
                                      lift (Std.Usize.wrapping_add proof_start
                                        8#usize)
                                    let i3 ← Slice.index_usize val4 i2
                                    let i4 ←
                                      NMT_call_3
                                        aspis_r1_cost_probe.transport.Variant.S2
                                    if i3 != i4
                                    then
                                      ok (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let p ←
                                        NMT_call_5
                                          val2
                                      let s1 ←
                                        core.slice.index.Slice.index
                                          (core.slice.index.SliceIndexRangeUsizeSlice
                                          Std.U8) val4
                                          {
                                            start := proof_start,
                                            «end» := val5
                                          }
                                      let i5 ← Slice.index_usize data 1#usize
                                      let i6 ← lift (UScalar.cast .Usize i5)
                                      let r14 ← NMT_call_11 p val1 s1 i6
                                      let cf12 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r14
                                      match cf12 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val6 =>
                                        let i7 := alloc.vec.Vec.len val6
                                        let i8 := Slice.len val
                                        if i7 != i8
                                        then
                                          ok (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else ok (core.result.Result.Ok val6)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (alloc.vec.Vec Std.U8)
                                          (core.convert.FromSame
                                          solana_program_error.ProgramError)
                                          residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                  solana_program_error.ProgramError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
    else
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)


end PRVFresh_C19_F10_i1

theorem PRVEq.C19_F10.NMT_stage1_owned.stage1_owned_i1 :
    @NMT_stage1_owned.PRVFresh_C19_F10_i1.r1_pool_adapter.owned.stage1_owned =
    @NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned := rfl
#print axioms PRVEq.C19_F10.NMT_stage1_owned.stage1_owned_i1
end NMT_stage1_owned

end
end PRVBundle_10
section PRVBundle_11
-- PCVI_ item 3 (Port23PUSH push, update_residue_row): derived from the P2f generated file; the two dropped definitions are restored with the library call
-- MutAArray...into_iter replaced by the parameter arrayIntoIter (gate ArrayIntoIter). CONDITIONAL_ON_BINDING (HM-B/HM-D library row).
-- GENERATED (base) by PCUF_gen_equalities.py for gate module Port23PUSH_Source. Statements are against the gate constants of Port23PUSH_Source.
-- fresh emission: PCQF_aspis_r1_cost_probe_candidate -> PRVFresh_C19_F11_Port23PUSH_Source; fresh source sha256 04b39d856d9a1432f3b69a8875e808bbe4aad5fabb4f374314366435d7eb6884
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace Port23PUSH
namespace PRVFresh_C19_F11_Port23PUSH_Source
/- PRVE name-map alias (recorded in the report; the Types pass of the same emission checks the identity): fresh type aspis_core.field.CM31 is the gate type field.CM31 -/
abbrev aspis_core.field.CM31 := Port23PUSH.field.CM31
/- PRVE name-map alias (recorded in the report; the Types pass of the same emission checks the identity): fresh type aspis_core.field.M31 is the gate type field.M31 -/
abbrev aspis_core.field.M31 := Port23PUSH.field.M31
/- PRVE name-map alias (recorded in the report; the Types pass of the same emission checks the identity): fresh type aspis_core.field.QM31 is the gate type field.QM31 -/
abbrev aspis_core.field.QM31 := Port23PUSH.field.QM31

/-- [aspis_r1_cost_probe::verifier::power_limb_at]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 233:0-233:64 -/
def verifier.power_limb_at
  (limbs : Array Std.U32 4#usize) (index : Std.Usize) : Result Std.U32 := do
  Array.index_usize limbs index

/-- [aspis_r1_cost_probe::verifier::residue_limb_at]:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 231:0-231:62 -/
def verifier.residue_limb_at
  (row : Array Std.U64 4#usize) (index : Std.Usize) : Result Std.U64 := do
  Array.index_usize row index

/-- [aspis_r1_cost_probe::verifier::update_residue_row]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 237:4-241:5 -/
def verifier.update_residue_row_loop0.body
  (limbs : Array Std.U32 4#usize) (iter : core.ops.range.Range Std.Usize)
  (row : Array Std.U64 4#usize) (basis : aspis_core.field.M31) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize) × aspis_core.field.M31) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done row)
  | some j =>
    let old ← verifier.residue_limb_at row j
    let limb ← verifier.power_limb_at limbs j
    let i ← lift (core.convert.num.FromU64U32.from limb)
    let i1 ← lift (core.convert.num.FromU64U32.from basis)
    let i2 ← i * i1
    let i3 ← old + i2
    let row1 ← Array.update row j i3
    ok (cont (iter1, row1, basis))

/-- [aspis_r1_cost_probe::verifier::update_residue_row]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 237:4-241:5 -/
def verifier.update_residue_row_loop0
  (iter : core.ops.range.Range Std.Usize) (row : Array Std.U64 4#usize)
  (basis : aspis_core.field.M31) (limbs : Array Std.U32 4#usize) :
  Result (Array Std.U64 4#usize)
  := do
  loop
    (fun (iter1, row1, basis1) => verifier.update_residue_row_loop0.body limbs
      iter1 row1 basis1)
    (iter, row, basis)

/-- [aspis_r1_cost_probe::verifier::update_residue_row]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 243:8-243:64 -/
def verifier.update_residue_row_loop1.body
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (fun im => let im1 := next_back im none
                                back im1))
  | some limb =>
    let i ← lift (limb &&& 2147483647#u64)
    let i1 ← limb >>> 31#i32
    let limb1 ← i + i1
    ok (cont (iter1, fun im => let im1 := next_back im (some limb1)
                               back im1))

/-- [aspis_r1_cost_probe::verifier::update_residue_row]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 243:8-243:64 -/
def verifier.update_residue_row_loop1
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  := do
  loop
    (fun (iter1, back1) => verifier.update_residue_row_loop1.body iter1 back1)
    (iter, back)

/-- [aspis_r1_cost_probe::verifier::update_residue_row]; the library call MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter is the parameter arrayIntoIter.
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 235:0-245:1 -/
def verifier.update_residue_row (arrayIntoIter : Port23PUSH.ArrayIntoIter)
  (row : Array Std.U64 4#usize) (power : aspis_core.field.QM31)
  (basis : aspis_core.field.M31) (flush : Bool) :
  Result (Array Std.U64 4#usize)
  := do
  let i := power.c0.a
  let i1 := power.c0.b
  let i2 := power.c1.a
  let i3 := power.c1.b
  let row1 ←
    verifier.update_residue_row_loop0 { start := 0#usize, «end» := 4#usize }
      row basis (Array.make 4#usize [ i, i1, i2, i3 ])
  if flush
  then
    let (iter, into_iter_back) ← arrayIntoIter row1
    let back ← verifier.update_residue_row_loop1 iter (fun im => im)
    ok (into_iter_back back)
  else ok row1

/-- [aspis_r1_cost_probe::verifier::{aspis_r1_cost_probe::verifier::BatchedWeights}::push]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 217:4-220:5 -/
def verifier.BatchedWeights.push (arrayIntoIter : Port23PUSH.ArrayIntoIter)
  (self : verifier.BatchedWeights) (index : Std.Usize)
  (power : aspis_core.field.QM31) (basis : aspis_core.field.M31) :
  Result verifier.BatchedWeights
  := do
  let i ← lift (self.terms &&& 3#usize)
  let (a, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array
      Std.U64 4#usize)) self.«raw» index
  let a1 ← verifier.update_residue_row arrayIntoIter a power basis (i = 3#usize)
  let v := index_mut_back a1
  ok { self with «raw» := v }

end PRVFresh_C19_F11_Port23PUSH_Source
end Port23PUSH

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F11.Port23PUSH_Source.verifier.power_limb_at : @Port23PUSH.PRVFresh_C19_F11_Port23PUSH_Source.verifier.power_limb_at = @Port23PUSH.verifier.power_limb_at := by
  (trace "PRV-S1 PRVEq.C19_F11.Port23PUSH_Source.verifier.power_limb_at"; rfl)
#print axioms PRVEq.C19_F11.Port23PUSH_Source.verifier.power_limb_at

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F11.Port23PUSH_Source.verifier.residue_limb_at : @Port23PUSH.PRVFresh_C19_F11_Port23PUSH_Source.verifier.residue_limb_at = @Port23PUSH.verifier.residue_limb_at := by
  (trace "PRV-S1 PRVEq.C19_F11.Port23PUSH_Source.verifier.residue_limb_at"; rfl)
#print axioms PRVEq.C19_F11.Port23PUSH_Source.verifier.residue_limb_at

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop0.body : @Port23PUSH.PRVFresh_C19_F11_Port23PUSH_Source.verifier.update_residue_row_loop0.body = @Port23PUSH.verifier.update_residue_row_loop0.body := by
  (trace "PRV-S1 PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop0.body"; rfl)
#print axioms PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop0.body

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop0 : @Port23PUSH.PRVFresh_C19_F11_Port23PUSH_Source.verifier.update_residue_row_loop0 = @Port23PUSH.verifier.update_residue_row_loop0 := by
  (trace "PRV-S1 PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop0"; rfl)
#print axioms PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop0

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop1.body : @Port23PUSH.PRVFresh_C19_F11_Port23PUSH_Source.verifier.update_residue_row_loop1.body = @Port23PUSH.verifier.update_residue_row_loop1.body := by
  (trace "PRV-S1 PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop1.body"; rfl)
#print axioms PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop1.body

set_option maxHeartbeats 200000 in
theorem PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop1 : @Port23PUSH.PRVFresh_C19_F11_Port23PUSH_Source.verifier.update_residue_row_loop1 = @Port23PUSH.verifier.update_residue_row_loop1 := by
  (trace "PRV-S1 PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop1"; rfl)
#print axioms PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_loop1


theorem PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_i1 (f : Port23PUSH.ArrayIntoIter) :
    @Port23PUSH.PRVFresh_C19_F11_Port23PUSH_Source.verifier.update_residue_row f = @Port23PUSH.verifier.update_residue_row f := by
  rfl
#print axioms PRVEq.C19_F11.Port23PUSH_Source.verifier.update_residue_row_i1

theorem PRVEq.C19_F11.Port23PUSH_Source.verifier.BatchedWeights.push_i1 (f : Port23PUSH.ArrayIntoIter) :
    @Port23PUSH.PRVFresh_C19_F11_Port23PUSH_Source.verifier.BatchedWeights.push f = @Port23PUSH.verifier.BatchedWeights.push f := by
  rfl
#print axioms PRVEq.C19_F11.Port23PUSH_Source.verifier.BatchedWeights.push_i1

end
end PRVBundle_11
section PRVBundle_12
-- PCVI_ item 3 FIp four_dots family, shape i9 (i8 minus helpers that depend on canonical.reduce; i7 minus the four statements that fail on a checked-vs-wrapping configuration mismatch of the gate callees canonical.reduce and EbyKDot.push, recorded in PCVI_CLASSIFICATIONS.json; i4 simp timed out on four_dots_one; i3 definitions only; i1 timed out at 180 s, i2 unknown constants; from_le_bytes callees mapped to the gate module RPz7_FIp_DotDecode) (undropped 6 blocks, 5 obligations as rfl attempts)
-- GENERATED by PCUE_gen_equalities.py for gate module RPz7_FIp_NativeDots. Statements are against the gate constants of RPz7_FIp_NativeDots.
-- fresh emission: PCQC_aspis_r1_cost_probe_candidate -> PRVFresh_C19_F12_RPz7_FIp_NativeDots; fresh source sha256 9d636b104d29f158a103fb12bd5e4e2cc12e78fdec42978f1a8c893d85fcd941
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1.FIp_NativeDots
namespace PRVFresh_C19_F12_RPz7_FIp_NativeDots
open FIo_Native

/-- [aspis_r1_cost_probe::fast_pairing::canonical::P]
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 5:4-5:32
    Visibility: public -/
@[global_simps, irreducible]
def fast_pairing.canonical.P : Std.U32 := 2147483647#u32

/-- [aspis_r1_cost_probe::fast_pairing::canonical::reduce]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 10:22-14:5 -/
def fast_pairing.canonical.reduce (x : Std.U64) : Result Std.U32 := do
  let i ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let i6 ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
  if x2 >= i6
  then
    let i7 ← lift (core.convert.num.FromU64U32.from fast_pairing.canonical.P)
    let i8 ← x2 - i7
    ok (UScalar.cast .U32 i8)
  else ok (UScalar.cast .U32 x2)

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Dot}::finish]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 123:8-123:121
    Visibility: public -/
def fast_pairing.canonical.Dot.finish
  (self : fast_pairing.canonical.Dot) : Result fast_pairing.canonical.Q := do
  let i ← Array.index_usize self.sums 0#usize
  let i1 ← fast_pairing.canonical.reduce i
  let i2 ← Array.index_usize self.sums 1#usize
  let i3 ← fast_pairing.canonical.reduce i2
  let i4 ← Array.index_usize self.sums 2#usize
  let i5 ← fast_pairing.canonical.reduce i4
  let i6 ← Array.index_usize self.sums 3#usize
  let i7 ← fast_pairing.canonical.reduce i6
  ok (Array.make 4#usize [ i1, i3, i5, i7 ])

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Q}::limbs]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 29:8-29:49
    Visibility: public -/
def fast_pairing.canonical.Q.limbs
  (self : fast_pairing.canonical.Q) : Result (Array Std.U32 4#usize) := do
  ok self

/-- [aspis_r1_cost_probe::fast_pairing::{aspis_r1_cost_probe::fast_pairing::EbyKDot}::finish]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 176:4-181:5
    Visibility: public -/
def fast_pairing.EbyKDot.finish
  (self : fast_pairing.EbyKDot) :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let q ← fast_pairing.canonical.Dot.finish self.c0
  let a ← fast_pairing.canonical.Q.limbs q
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let q1 ← fast_pairing.canonical.Dot.finish self.c1
  let a2 ← fast_pairing.canonical.Q.limbs q1
  let e ← Array.index_usize a2 0#usize
  let f ← Array.index_usize a2 1#usize
  let g ← Array.index_usize a2 2#usize
  let h ← Array.index_usize a2 3#usize
  let o ←
    aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [ a1, b, c, d, e, f, g, h ])
  core.option.Option.unwrap o

/-- [aspis_r1_cost_probe::fast_pairing::limbs_of]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 133:0-135:1 -/
def fast_pairing.limbs_of
  (k : aspis_core.field.QM31) : Result (Array Std.U32 4#usize) := do
  let i := k.c0.a
  let i1 := k.c0.b
  let i2 := k.c1.a
  let i3 := k.c1.b
  ok (Array.make 4#usize [ i, i1, i2, i3 ])

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Q}::from_limbs]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 24:8-27:9
    Visibility: public -/
def fast_pairing.canonical.Q.from_limbs
  (x : Array Std.U32 4#usize) : Result (Option fast_pairing.canonical.Q) := do
  let a ← Array.index_usize x 0#usize
  let b ← Array.index_usize x 1#usize
  let c ← Array.index_usize x 2#usize
  let d ← Array.index_usize x 3#usize
  if a < fast_pairing.canonical.P
  then
    if b < fast_pairing.canonical.P
    then
      if c < fast_pairing.canonical.P
      then
        if d < fast_pairing.canonical.P
        then ok (some (Array.make 4#usize [ a, b, c, d ]))
        else ok none
      else ok none
    else ok none
  else ok none

/-- [aspis_r1_cost_probe::fast_pairing::checked_q]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 138:0-140:1 -/
def fast_pairing.checked_q
  (k : aspis_core.field.QM31) :
  Result (core.result.Result fast_pairing.canonical.Q Unit)
  := do
  let a ← fast_pairing.limbs_of k
  let o ← fast_pairing.canonical.Q.from_limbs a
  match o with
  | none => ok (core.result.Result.Err ())
  | some q => ok (core.result.Result.Ok q)

/-- [aspis_r1_cost_probe::fast_pairing::MAX_TERMS]
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 130:0-130:30 -/
@[global_simps, irreducible]
def fast_pairing.MAX_TERMS : Std.Usize := 4096#usize

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Q}::from_wide]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 33:8-36:9 -/
def fast_pairing.canonical.Q.from_wide
  (value : aspis_core.field.wide_exact.WideExact) :
  Result (Array fast_pairing.canonical.Q 2#usize)
  := do
  let a ← aspis_core.field.wide_exact.WideExact.to_limbs value
  let a1 ← Array.index_usize a 0#usize
  let b ← Array.index_usize a 1#usize
  let c ← Array.index_usize a 2#usize
  let d ← Array.index_usize a 3#usize
  let e ← Array.index_usize a 4#usize
  let f ← Array.index_usize a 5#usize
  let g ← Array.index_usize a 6#usize
  let h ← Array.index_usize a 7#usize
  ok
    (Array.make 2#usize [
      Array.make 4#usize [ a1, b, c, d ], Array.make 4#usize [ e, f, g, h ]
      ])

/-- [aspis_r1_cost_probe::fast_pairing::{aspis_r1_cost_probe::fast_pairing::EbyKDot}::push]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 165:4-173:5
    Visibility: public -/
def fast_pairing.EbyKDot.push
  (self : fast_pairing.EbyKDot) (value : aspis_core.field.wide_exact.WideExact)
  (scalar : aspis_core.field.QM31) :
  Result ((core.result.Result Unit Unit) × fast_pairing.EbyKDot)
  := do
  if self.count >= fast_pairing.MAX_TERMS
  then ok (core.result.Result.Err (), self)
  else
    let a ← fast_pairing.canonical.Q.from_wide value
    let value_c0 ← Array.index_usize a 0#usize
    let value_c1 ← Array.index_usize a 1#usize
    let r ← fast_pairing.checked_q scalar
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let d ← fast_pairing.canonical.Dot.push self.c0 value_c0 val
      let d1 ← fast_pairing.canonical.Dot.push self.c1 value_c1 val
      let i ← self.count + 1#usize
      ok (core.result.Result.Ok (), { c0 := d, c1 := d1, count := i })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame Unit) residual
      ok (r1, self)

/-- [aspis_r1_cost_probe::fast_pairing::canonical::{aspis_r1_cost_probe::fast_pairing::canonical::Dot}::new]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 112:8-112:45
    Visibility: public -/
def fast_pairing.canonical.Dot.new : Result fast_pairing.canonical.Dot := do
  let a := Array.repeat 4#usize 0#u64
  ok { sums := a }

/-- [aspis_r1_cost_probe::fast_pairing::{aspis_r1_cost_probe::fast_pairing::EbyKDot}::new]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_pairing.rs', lines 160:4-162:5
    Visibility: public -/
def fast_pairing.EbyKDot.new : Result fast_pairing.EbyKDot := do
  let d ← fast_pairing.canonical.Dot.new
  ok { c0 := d, c1 := d, count := 0#usize }

/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop body 1:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 19:12-35:13 -/
def fast_dots.four_dots_one_loop0_loop0.body
  (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (sums : Array Std.U64 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    8#usize)) (Array Std.U64 8#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done sums)
  | some term =>
    let i ← slot * 120#usize
    let i1 ← term * 4#usize
    let i2 ← i + i1
    let i3 ← i + i1
    let i4 ← i3 + 4#usize
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
        { start := i2, «end» := i4 }
    let r ←
      core.array.TryFromArrayCopySlice.try_from 4#usize core.marker.CopyU8 s
    let a ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
    let o1 ← AspisR1.FIp_DotDecode.field.M31.from_le_bytes a
    let scalar ← core.option.Option.unwrap o1
    let we ← Array.index_usize g term
    let coefficient ← aspis_core.field.wide_exact.WideExact.to_limbs we
    let i5 ← Array.index_usize coefficient 0#usize
    let i6 ← lift (core.convert.num.FromU64U32.from i5)
    let i7 ← lift (core.convert.num.FromU64U32.from scalar)
    let i8 ← i6 * i7
    let i9 ← Array.index_usize sums 0#usize
    let i10 ← i9 + i8
    let sums1 ← Array.update sums 0#usize i10
    let i11 ← Array.index_usize coefficient 1#usize
    let i12 ← lift (core.convert.num.FromU64U32.from i11)
    let i13 ← lift (core.convert.num.FromU64U32.from scalar)
    let i14 ← i12 * i13
    let i15 ← Array.index_usize sums1 1#usize
    let i16 ← i15 + i14
    let sums2 ← Array.update sums1 1#usize i16
    let i17 ← Array.index_usize coefficient 2#usize
    let i18 ← lift (core.convert.num.FromU64U32.from i17)
    let i19 ← lift (core.convert.num.FromU64U32.from scalar)
    let i20 ← i18 * i19
    let i21 ← Array.index_usize sums2 2#usize
    let i22 ← i21 + i20
    let sums3 ← Array.update sums2 2#usize i22
    let i23 ← Array.index_usize coefficient 3#usize
    let i24 ← lift (core.convert.num.FromU64U32.from i23)
    let i25 ← lift (core.convert.num.FromU64U32.from scalar)
    let i26 ← i24 * i25
    let i27 ← Array.index_usize sums3 3#usize
    let i28 ← i27 + i26
    let sums4 ← Array.update sums3 3#usize i28
    let i29 ← Array.index_usize coefficient 4#usize
    let i30 ← lift (core.convert.num.FromU64U32.from i29)
    let i31 ← lift (core.convert.num.FromU64U32.from scalar)
    let i32 ← i30 * i31
    let i33 ← Array.index_usize sums4 4#usize
    let i34 ← i33 + i32
    let sums5 ← Array.update sums4 4#usize i34
    let i35 ← Array.index_usize coefficient 5#usize
    let i36 ← lift (core.convert.num.FromU64U32.from i35)
    let i37 ← lift (core.convert.num.FromU64U32.from scalar)
    let i38 ← i36 * i37
    let i39 ← Array.index_usize sums5 5#usize
    let i40 ← i39 + i38
    let sums6 ← Array.update sums5 5#usize i40
    let i41 ← Array.index_usize coefficient 6#usize
    let i42 ← lift (core.convert.num.FromU64U32.from i41)
    let i43 ← lift (core.convert.num.FromU64U32.from scalar)
    let i44 ← i42 * i43
    let i45 ← Array.index_usize sums6 6#usize
    let i46 ← i45 + i44
    let sums7 ← Array.update sums6 6#usize i46
    let i47 ← Array.index_usize coefficient 7#usize
    let i48 ← lift (core.convert.num.FromU64U32.from i47)
    let i49 ← lift (core.convert.num.FromU64U32.from scalar)
    let i50 ← i48 * i49
    let i51 ← Array.index_usize sums7 7#usize
    let i52 ← i51 + i50
    let sums8 ← Array.update sums7 7#usize i52
    ok (cont (iter1, sums8))

/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop 1:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 19:12-35:13 -/
def fast_dots.four_dots_one_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  (sums : Array Std.U64 8#usize) :
  Result (Array Std.U64 8#usize)
  := do
  loop
    (fun (iter1, sums1) => fast_dots.four_dots_one_loop0_loop0.body q g slot
      iter1 sums1)
    (iter, sums)

/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 17:8-44:9 -/
def fast_dots.four_dots_one_loop0.body
  (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (limbs : Array Std.U64 8#usize) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Std.Usize)) × (Array Std.U64 8#usize)) (Array Std.U64 8#usize))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done limbs)
  | some start =>
    let sums := Array.repeat 8#usize 0#u64
    let i ← start + 4#usize
    let i1 ← core.cmp.min core.cmp.OrdUsize i 26#usize
    let sums1 ←
      fast_dots.four_dots_one_loop0_loop0 { start, «end» := i1 } q g slot
        sums
    let i2 ← Array.index_usize sums1 0#usize
    let i3 ← lift (i2 &&& 2147483647#u64)
    let i4 ← i2 >>> 31#i32
    let i5 ← i3 + i4
    let i6 ← Array.index_usize limbs 0#usize
    let i7 ← i6 + i5
    let limbs1 ← Array.update limbs 0#usize i7
    let i8 ← Array.index_usize sums1 1#usize
    let i9 ← lift (i8 &&& 2147483647#u64)
    let i10 ← i8 >>> 31#i32
    let i11 ← i9 + i10
    let i12 ← Array.index_usize limbs1 1#usize
    let i13 ← i12 + i11
    let limbs2 ← Array.update limbs1 1#usize i13
    let i14 ← Array.index_usize sums1 2#usize
    let i15 ← lift (i14 &&& 2147483647#u64)
    let i16 ← i14 >>> 31#i32
    let i17 ← i15 + i16
    let i18 ← Array.index_usize limbs2 2#usize
    let i19 ← i18 + i17
    let limbs3 ← Array.update limbs2 2#usize i19
    let i20 ← Array.index_usize sums1 3#usize
    let i21 ← lift (i20 &&& 2147483647#u64)
    let i22 ← i20 >>> 31#i32
    let i23 ← i21 + i22
    let i24 ← Array.index_usize limbs3 3#usize
    let i25 ← i24 + i23
    let limbs4 ← Array.update limbs3 3#usize i25
    let i26 ← Array.index_usize sums1 4#usize
    let i27 ← lift (i26 &&& 2147483647#u64)
    let i28 ← i26 >>> 31#i32
    let i29 ← i27 + i28
    let i30 ← Array.index_usize limbs4 4#usize
    let i31 ← i30 + i29
    let limbs5 ← Array.update limbs4 4#usize i31
    let i32 ← Array.index_usize sums1 5#usize
    let i33 ← lift (i32 &&& 2147483647#u64)
    let i34 ← i32 >>> 31#i32
    let i35 ← i33 + i34
    let i36 ← Array.index_usize limbs5 5#usize
    let i37 ← i36 + i35
    let limbs6 ← Array.update limbs5 5#usize i37
    let i38 ← Array.index_usize sums1 6#usize
    let i39 ← lift (i38 &&& 2147483647#u64)
    let i40 ← i38 >>> 31#i32
    let i41 ← i39 + i40
    let i42 ← Array.index_usize limbs6 6#usize
    let i43 ← i42 + i41
    let limbs7 ← Array.update limbs6 6#usize i43
    let i44 ← Array.index_usize sums1 7#usize
    let i45 ← lift (i44 &&& 2147483647#u64)
    let i46 ← i44 >>> 31#i32
    let i47 ← i45 + i46
    let i48 ← Array.index_usize limbs7 7#usize
    let i49 ← i48 + i47
    let limbs8 ← Array.update limbs7 7#usize i49
    ok (cont (iter1, limbs8))

/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 17:8-44:9 -/
def fast_dots.four_dots_one_loop0
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize))
  (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  (limbs : Array Std.U64 8#usize) :
  Result (Array Std.U64 8#usize)
  := do
  loop
    (fun (iter1, limbs1) => fast_dots.four_dots_one_loop0.body q g slot iter1
      limbs1)
    (iter, limbs)

/-- [aspis_r1_cost_probe::fast_dots::four_dots_one]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 15:0-64:1 -/
def fast_dots.four_dots_one
  (q : Array Std.U8 608#usize)
  (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (slot : Std.Usize)
  :
  Result aspis_core.field.wide_exact.WideExact
  := do
  let limbs := Array.repeat 8#usize 0#u64
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» := 26#usize } 4#usize
  let limbs1 ← fast_dots.four_dots_one_loop0 iter q g slot limbs
  let i ← Array.index_usize limbs1 0#usize
  let m ← aspis_core.field.M31.reduce_u64 i
  let i1 ← Array.index_usize limbs1 1#usize
  let m1 ← aspis_core.field.M31.reduce_u64 i1
  let i2 ← Array.index_usize limbs1 2#usize
  let m2 ← aspis_core.field.M31.reduce_u64 i2
  let i3 ← Array.index_usize limbs1 3#usize
  let m3 ← aspis_core.field.M31.reduce_u64 i3
  let i4 ← Array.index_usize limbs1 4#usize
  let m4 ← aspis_core.field.M31.reduce_u64 i4
  let i5 ← Array.index_usize limbs1 5#usize
  let m5 ← aspis_core.field.M31.reduce_u64 i5
  let i6 ← Array.index_usize limbs1 6#usize
  let m6 ← aspis_core.field.M31.reduce_u64 i6
  let i7 ← Array.index_usize limbs1 7#usize
  let m7 ← aspis_core.field.M31.reduce_u64 i7
  let o ←
    aspis_core.field.wide_exact.WideExact.from_limbs
      (Array.make 8#usize [ m, m1, m2, m3, m4, m5, m6, m7 ])
  let value ← core.option.Option.unwrap o
  let tail ← fast_pairing.EbyKDot.new
  let we ← Array.index_usize g 28#usize
  let i8 ← slot * 120#usize
  let i9 ← i8 + 104#usize
  let i10 ← i8 + 120#usize
  let s ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := i9, «end» := i10 }
  let o1 ← AspisR1.FIp_DotDecode.field.QM31.from_le_bytes s
  let q1 ← core.option.Option.unwrap o1
  let (r, tail1) ← fast_pairing.EbyKDot.push tail we q1
  core.result.Result.unwrap core.fmt.DebugUnit r
  let i11 ← slot * 32#usize
  let i12 ← 480#usize + i11
  let i13 ← 0#usize * 16#usize
  let offset0 ← i12 + i13
  let i14 ← 0#usize + 26#usize
  let we1 ← Array.index_usize g i14
  let i15 ← offset0 + 16#usize
  let s1 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := offset0, «end» := i15 }
  let o2 ← AspisR1.FIp_DotDecode.field.QM31.from_le_bytes s1
  let q2 ← core.option.Option.unwrap o2
  let (r1, tail2) ← fast_pairing.EbyKDot.push tail1 we1 q2
  core.result.Result.unwrap core.fmt.DebugUnit r1
  let i16 ← 480#usize + i11
  let i17 ← 1#usize * 16#usize
  let offset1 ← i16 + i17
  let i18 ← 1#usize + 26#usize
  let we2 ← Array.index_usize g i18
  let i19 ← offset1 + 16#usize
  let s2 ←
    core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) q
      { start := offset1, «end» := i19 }
  let o3 ← AspisR1.FIp_DotDecode.field.QM31.from_le_bytes s2
  let q3 ← core.option.Option.unwrap o3
  let (r2, tail3) ← fast_pairing.EbyKDot.push tail2 we2 q3
  core.result.Result.unwrap core.fmt.DebugUnit r2
  let we3 ← fast_pairing.EbyKDot.finish tail3
  aspis_core.field.wide_exact.WideExact.add value we3

/-- [aspis_r1_cost_probe::fast_dots::four_dots]:
    Source: 'crates/aspis-r1-cost-probe/src/fast_dots.rs', lines 67:0-75:1
    Visibility: public -/
def fast_dots.four_dots
  (q : Slice Std.U8) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
  :
  Result (Array aspis_core.field.wide_exact.WideExact 4#usize)
  := do
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U8) q { «end» := 608#usize }
  let r ← core.array.TryFromSharedArraySlice.try_from 608#usize s
  let q1 ← core.result.Result.unwrap core.fmt.DebugTryFromSliceError r
  let we ← fast_dots.four_dots_one q1 g 0#usize
  let we1 ← fast_dots.four_dots_one q1 g 1#usize
  let we2 ← fast_dots.four_dots_one q1 g 2#usize
  let we3 ← fast_dots.four_dots_one q1 g 3#usize
  ok (Array.make 4#usize [ we, we1, we2, we3 ])

end PRVFresh_C19_F12_RPz7_FIp_NativeDots
end AspisR1.FIp_NativeDots

-- obligation (not attempted in this shape): PRVEq.C19_F12.RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0

-- obligation (not attempted in this shape): PRVEq.C19_F12.RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0.body

-- obligation (not attempted in this shape): PRVEq.C19_F12.RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0

-- obligation (not attempted in this shape): PRVEq.C19_F12.RPz7_FIp_NativeDots.fast_dots.four_dots_one

-- obligation (not attempted in this shape): PRVEq.C19_F12.RPz7_FIp_NativeDots.fast_dots.four_dots


theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_loop0.body_i4 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body = @AspisR1.FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body := by
  delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body AspisR1.FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body
  all_goals rfl
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_loop0.body_i4

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_loop0_i4 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 = @AspisR1.FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 := by
  delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 AspisR1.FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0
  simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_loop0.body_i4]
  all_goals rfl
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_loop0_i4

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0.body_i4 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0.body = @AspisR1.FIp_NativeDots.fast_dots.four_dots_one_loop0.body := by
  delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0.body AspisR1.FIp_NativeDots.fast_dots.four_dots_one_loop0.body
  simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_loop0.body_i4, PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_loop0_i4]
  all_goals rfl
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0.body_i4

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_i4 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0 = @AspisR1.FIp_NativeDots.fast_dots.four_dots_one_loop0 := by
  delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_dots.four_dots_one_loop0 AspisR1.FIp_NativeDots.fast_dots.four_dots_one_loop0
  simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_loop0.body_i4, PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_loop0_i4, PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0.body_i4]
  all_goals rfl
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_loop0_i4

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_P_i7 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.canonical.P = @FIo_Native.fast_pairing.canonical.P := by
  first | rfl | (delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.canonical.P FIo_Native.fast_pairing.canonical.P; all_goals rfl)
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_P_i7

-- not attempted in this shape / failed in PCVI_L017:

-- dropped in this shape (depends on canonical.reduce):

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_limbs_i7 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.canonical.Q.limbs = @FIo_Native.fast_pairing.canonical.Q.limbs := by
  first | rfl | (delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.canonical.Q.limbs FIo_Native.fast_pairing.canonical.Q.limbs; (try simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_P_i7]); all_goals rfl)
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_limbs_i7

-- dropped in this shape (depends on canonical.reduce):

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.H_limbs_of_i7 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.limbs_of = @FIo_Native.fast_pairing.limbs_of := by
  first | rfl | (delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.limbs_of FIo_Native.fast_pairing.limbs_of; (try simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_P_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_limbs_i7]); all_goals rfl)
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.H_limbs_of_i7

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_from_limbs_i7 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.canonical.Q.from_limbs = @FIo_Native.fast_pairing.canonical.Q.from_limbs := by
  first | rfl | (delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.canonical.Q.from_limbs FIo_Native.fast_pairing.canonical.Q.from_limbs; (try simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_P_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_limbs_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_limbs_of_i7]); all_goals rfl)
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_from_limbs_i7

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.H_checked_q_i7 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.checked_q = @FIo_Native.fast_pairing.checked_q := by
  first | rfl | (delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.checked_q FIo_Native.fast_pairing.checked_q; (try simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_P_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_limbs_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_limbs_of_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_from_limbs_i7]); all_goals rfl)
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.H_checked_q_i7

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.H_MAX_TERMS_i7 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.MAX_TERMS = @FIo_Native.fast_pairing.MAX_TERMS := by
  first | rfl | (delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.MAX_TERMS FIo_Native.fast_pairing.MAX_TERMS; (try simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_P_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_limbs_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_limbs_of_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_from_limbs_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_checked_q_i7]); all_goals rfl)
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.H_MAX_TERMS_i7

-- dropped in this shape (depends on canonical.reduce):

-- not attempted in this shape / failed in PCVI_L017:

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Dot_new_i7 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.canonical.Dot.new = @FIo_Native.fast_pairing.canonical.Dot.new := by
  first | rfl | (delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.canonical.Dot.new FIo_Native.fast_pairing.canonical.Dot.new; (try simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_P_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_limbs_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_limbs_of_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_from_limbs_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_checked_q_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_MAX_TERMS_i7]); all_goals rfl)
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Dot_new_i7

theorem PRVEq.C19_F12.RPz7_FIp_NativeDots.H_EbyKDot_new_i7 : @AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.EbyKDot.new = @FIo_Native.fast_pairing.EbyKDot.new := by
  first | rfl | (delta AspisR1.FIp_NativeDots.PRVFresh_C19_F12_RPz7_FIp_NativeDots.fast_pairing.EbyKDot.new FIo_Native.fast_pairing.EbyKDot.new; (try simp only [PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_P_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_limbs_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_limbs_of_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Q_from_limbs_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_checked_q_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_MAX_TERMS_i7, PRVEq.C19_F12.RPz7_FIp_NativeDots.H_canonical_Dot_new_i7]); all_goals rfl)
#print axioms PRVEq.C19_F12.RPz7_FIp_NativeDots.H_EbyKDot_new_i7

-- not attempted in this shape / failed in PCVI_L017: PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_one_i4

-- not attempted in this shape / failed in PCVI_L017: PRVEq.C19_F12.RPz7_FIp_NativeDots.four_dots_i4


end
end PRVBundle_12
section PRVBundle_13
-- PCVI_ item 1: S1NativeCompact expand_semantic, expand_semantic_loop, expand_semantic_loop.body (CONDITIONAL_ON_BINDING).
-- Fresh text: prov-p2d-20261109/inputs/fresh_S1NativeCompactModelV1/Funs.lean (XRn_Join_Release emission of frozen 4bb3b3f, overflow ON).
-- Changes to the emission text, all mechanical: the namespace prefix _root_.XRn_Join_Release. is dropped (names resolve to PRVF);
-- the external compact.expand_values is replaced by a parameter `ext`; CodecError is read as the gate type
-- AspisR1CurrentCaller.compact.CodecError (gate abbrev compact.CodecError; same constructor Length).
-- Statements are fresh = gate against compiled gate constants. Binding (ext = the frozen compact.expand_values) stays at the instantiation.
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace AspisS1NativeCompact
namespace PRVF

/-- [aspis_r1_cost_probe::compact::SEMANTIC_COMPACT_VALUES]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 33:0-33:72
    Visibility: public -/
@[global_simps, irreducible]
def compact.SEMANTIC_COMPACT_VALUES : Result Std.Usize := do
  let i ← 10#usize * 28#usize
  let i1 ← 1#usize + i
  let i2 ← 87#usize + 29#usize
  let i3 ← i1 + i2
  i3 + 29#usize

/-- [aspis_r1_cost_probe::verifier::SEMANTIC_BYTES]
    Source: 'crates/aspis-r1-cost-probe/src/verifier.rs', lines 8:0-8:43
    Visibility: public -/
@[global_simps, irreducible]
def verifier.SEMANTIC_BYTES : Result Std.Usize := do
  let i ← 29#usize * 32#usize
  12903#usize + i

/-- [aspis_r1_cost_probe::compact::LOGICAL_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 31:0-31:68
    Visibility: public -/
@[global_simps, irreducible]
def compact.LOGICAL_SEMANTIC : Result Std.Usize := verifier.SEMANTIC_BYTES

/-- [aspis_r1_cost_probe::compact::COMPACT_SEMANTIC]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 34:0-34:84
    Visibility: public -/
@[global_simps, irreducible]
def compact.COMPACT_SEMANTIC : Result Std.Usize := do
  let i ← compact.SEMANTIC_COMPACT_VALUES
  let i1 ← 16#usize * i
  let i2 ← compact.LOGICAL_SEMANTIC
  i2 - i1

/-- [aspis_r1_cost_probe::r1_wire::POINTS]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 14:0-14:28
    Visibility: public -/
@[global_simps, irreducible] def r1_wire.POINTS : Std.Usize := 3#usize

/-- [aspis_r1_cost_probe::r1_wire::LANES]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 13:0-13:28
    Visibility: public -/
@[global_simps, irreducible] def r1_wire.LANES : Std.Usize := 29#usize

/-- [aspis_r1_cost_probe::r1_wire::CLAIMS]
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 15:0-15:41
    Visibility: public -/
@[global_simps, irreducible]
def r1_wire.CLAIMS : Result Std.Usize := r1_wire.POINTS * r1_wire.LANES

/-- [aspis_r1_cost_probe::r1_wire::row_shape]:
    Source: 'crates/aspis-r1-cost-probe/src/r1_wire.rs', lines 39:0-49:1
    Visibility: public -/
def r1_wire.row_shape
  (row : Std.U8) : Result (Option (Std.U8 × Std.Usize)) := do
  match row with
  | 0#uscalar => ok (some (0#u8, 0#usize))
  | 1#uscalar => ok (some (0#u8, 0#usize))
  | 2#uscalar => ok (some (1#u8, 32#usize))
  | 14#uscalar => ok (some (3#u8, 32#usize))
  | 25#uscalar =>
    let i ← r1_wire.CLAIMS
    let i1 ← i + r1_wire.LANES
    let i2 ← i1 * 32#usize
    ok (some (4#u8, i2))
  | 26#uscalar => let i ← r1_wire.LANES * 32#usize
                  ok (some (5#u8, i))
  | _ =>
    if 3#u8 <= row
    then
      if row <= 13#u8
      then ok (some (0#u8, 0#usize))
      else
        if 15#u8 <= row
        then
          if row <= 24#u8
          then let i ← 28#usize * 32#usize
               ok (some (2#u8, i))
          else ok none
        else ok none
    else
      if 15#u8 <= row
      then
        if row <= 24#u8
        then let i ← 28#usize * 32#usize
             ok (some (2#u8, i))
        else ok none
      else ok none

/-- [aspis_r1_cost_probe::compact::compact_row]:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 80:0-82:1 -/
def compact.compact_row (row : Std.U8) : Result Bool := do
  ok (row >= 14#u8)

/-- [aspis_r1_cost_probe::compact::SEMANTIC_ROWS]
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 29:0-29:33
    Visibility: public -/
@[global_simps, irreducible] def compact.SEMANTIC_ROWS : Std.U8 := 27#u8

/-- [aspis_r1_cost_probe::input::expand_semantic]: loop body 0:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 154:4-172:1
    Visibility: public -/
@[rust_loop_body]
def compact.expand_semantic_loop.body
  (ext : Slice Std.U8 → Slice Std.U8 → Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × Slice Std.U8))
  (input : Slice Std.U8) (iter : core.ops.range.Range Std.U8)
  (out : Slice Std.U8) (src : Std.Usize) (dst : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.U8) × (Slice Std.U8) ×
    Std.Usize × Std.Usize) ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) ×
    (Slice Std.U8)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepU8 iter
  match o with
  | none =>
    let i := Slice.len input
    if src != i
    then ok (done (core.result.Result.Err AspisR1CurrentCaller.compact.CodecError.Length, out))
    else
      let i1 := Slice.len out
      if dst != i1
      then ok (done (core.result.Result.Err AspisR1CurrentCaller.compact.CodecError.Length, out))
      else ok (done (core.result.Result.Ok (), out))
  | some row =>
    let o1 ← r1_wire.row_shape row
    let r ← core.option.Option.ok_or o1 AspisR1CurrentCaller.compact.CodecError.Length
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (_, size) := val
      let i ← dst + 5#usize
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out
          { start := dst, «end» := i }
      let i1 ← src + 5#usize
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) input
          { start := src, «end» := i1 }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let out1 := index_mut_back s2
      let b ← compact.compact_row row
      if b
      then
        let i2 ← size / 2#usize
        let i3 ← i1 + i2
        let s3 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) input
            { start := i1, «end» := i3 }
        let i4 ← i + size
        let (s4, index_mut_back1) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out1
            { start := i, «end» := i4 }
        let (r1, s5) ← ext s3 s4
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let out2 := index_mut_back1 s5
          let src1 ← i1 + i2
          ok (cont (iter1, out2, src1, i4))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r2 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame AspisR1CurrentCaller.compact.CodecError) residual
          let out2 := index_mut_back1 s5
          ok (done (r2, out2))
      else
        let i2 ← i + size
        let (s3, index_mut_back1) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) out1
            { start := i, «end» := i2 }
        let i3 ← i1 + size
        let s4 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) input
            { start := i1, «end» := i3 }
        let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
        let out2 := index_mut_back1 s5
        ok (cont (iter1, out2, i3, i2))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame AspisR1CurrentCaller.compact.CodecError) residual
      ok (done (r1, out))

/-- [aspis_r1_cost_probe::input::expand_semantic]: loop 0:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 154:4-172:1
    Visibility: public -/
@[rust_loop]
def compact.expand_semantic_loop
  (ext : Slice Std.U8 → Slice Std.U8 → Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × Slice Std.U8))
  (iter : core.ops.range.Range Std.U8) (input : Slice Std.U8)
  (out : Slice Std.U8) (src : Std.Usize) (dst : Std.Usize) :
  Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × (Slice Std.U8))
  := do
  loop
    (fun (iter1, out1, src1, dst1) => compact.expand_semantic_loop.body ext input
      iter1 out1 src1 dst1)
    (iter, out, src, dst)

/-- [aspis_r1_cost_probe::input::expand_semantic]:
    Source: 'crates/aspis-r1-cost-probe/src/compact.rs', lines 148:0-172:1
    Visibility: public -/
def compact.expand_semantic
  (ext : Slice Std.U8 → Slice Std.U8 → Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × Slice Std.U8))
  (input : Slice Std.U8) (out : Slice Std.U8) :
  Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × (Slice Std.U8))
  := do
  let i := Slice.len input
  let i1 ← compact.COMPACT_SEMANTIC
  if i != i1
  then ok (core.result.Result.Err AspisR1CurrentCaller.compact.CodecError.Length, out)
  else
    let i2 := Slice.len out
    let i3 ← compact.LOGICAL_SEMANTIC
    if i2 != i3
    then ok (core.result.Result.Err AspisR1CurrentCaller.compact.CodecError.Length, out)
    else
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) out
          { «end» := 32#usize }
      let s1 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) input
          { «end» := 32#usize }
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let out1 := index_mut_back s2
      compact.expand_semantic_loop ext
        { start := 0#u8, «end» := compact.SEMANTIC_ROWS } input out1
        32#usize 32#usize

end PRVF

open AspisS1NativeCompact

theorem PRVEq.C19_F13.S1NC.SEMANTIC_COMPACT_VALUES_i1 : @PRVF.compact.SEMANTIC_COMPACT_VALUES = @AspisS1NativeCompact.compact.SEMANTIC_COMPACT_VALUES := by
  delta PRVF.compact.SEMANTIC_COMPACT_VALUES AspisS1NativeCompact.compact.SEMANTIC_COMPACT_VALUES; rfl
theorem PRVEq.C19_F13.S1NC.SEMANTIC_BYTES_i1 : @PRVF.verifier.SEMANTIC_BYTES = @AspisS1NativeCompact.verifier.SEMANTIC_BYTES := by
  delta PRVF.verifier.SEMANTIC_BYTES AspisS1NativeCompact.verifier.SEMANTIC_BYTES; rfl
theorem PRVEq.C19_F13.S1NC.LOGICAL_SEMANTIC_i1 : @PRVF.compact.LOGICAL_SEMANTIC = @AspisS1NativeCompact.compact.LOGICAL_SEMANTIC := by
  delta PRVF.compact.LOGICAL_SEMANTIC AspisS1NativeCompact.compact.LOGICAL_SEMANTIC
  rw [PRVEq.C19_F13.S1NC.SEMANTIC_BYTES_i1]
theorem PRVEq.C19_F13.S1NC.COMPACT_SEMANTIC_i1 : @PRVF.compact.COMPACT_SEMANTIC = @AspisS1NativeCompact.compact.COMPACT_SEMANTIC := by
  delta PRVF.compact.COMPACT_SEMANTIC AspisS1NativeCompact.compact.COMPACT_SEMANTIC
  rw [PRVEq.C19_F13.S1NC.SEMANTIC_COMPACT_VALUES_i1, PRVEq.C19_F13.S1NC.LOGICAL_SEMANTIC_i1]
/-- Encoding difference: the emission constant is a plain Usize, the gate constant is Result-wrapped. -/
theorem PRVEq.C19_F13.S1NC.POINTS_i1 : (ok PRVF.r1_wire.POINTS : Result Std.Usize) = AspisS1NativeCompact.r1_wire.POINTS := by
  delta PRVF.r1_wire.POINTS AspisS1NativeCompact.r1_wire.POINTS; rfl
theorem PRVEq.C19_F13.S1NC.LANES_i1 : @PRVF.r1_wire.LANES = @AspisS1NativeCompact.r1_wire.LANES := by
  delta PRVF.r1_wire.LANES AspisS1NativeCompact.r1_wire.LANES; rfl
theorem PRVEq.C19_F13.S1NC.CLAIMS_i1 : @PRVF.r1_wire.CLAIMS = @AspisS1NativeCompact.r1_wire.CLAIMS := by
  delta PRVF.r1_wire.CLAIMS AspisS1NativeCompact.r1_wire.CLAIMS
  rw [← PRVEq.C19_F13.S1NC.POINTS_i1, PRVEq.C19_F13.S1NC.LANES_i1]; rfl
theorem PRVEq.C19_F13.S1NC.row_shape_i1 : @PRVF.r1_wire.row_shape = @AspisS1NativeCompact.r1_wire.row_shape := by
  funext row
  delta PRVF.r1_wire.row_shape AspisS1NativeCompact.r1_wire.row_shape
  rw [PRVEq.C19_F13.S1NC.CLAIMS_i1, PRVEq.C19_F13.S1NC.LANES_i1]
  all_goals rfl
theorem PRVEq.C19_F13.S1NC.compact_row_i1 : @PRVF.compact.compact_row = @AspisS1NativeCompact.compact.compact_row := rfl
theorem PRVEq.C19_F13.S1NC.SEMANTIC_ROWS_i1 : @PRVF.compact.SEMANTIC_ROWS = @AspisS1NativeCompact.compact.SEMANTIC_ROWS := by
  delta PRVF.compact.SEMANTIC_ROWS AspisS1NativeCompact.compact.SEMANTIC_ROWS; rfl

theorem PRVEq.C19_F13.S1NC.expand_semantic_loop.body_i1 (ops : AspisS1NativeCompact.Ops) :
    @PRVF.compact.expand_semantic_loop.body ops.expandValues = @AspisS1NativeCompact.compact.expand_semantic_loop.body ops := by
  funext input iter out src dst
  delta PRVF.compact.expand_semantic_loop.body AspisS1NativeCompact.compact.expand_semantic_loop.body
  simp only [PRVEq.C19_F13.S1NC.row_shape_i1, PRVEq.C19_F13.S1NC.compact_row_i1]
  all_goals rfl

theorem PRVEq.C19_F13.S1NC.expand_semantic_loop_i1 (ops : AspisS1NativeCompact.Ops) :
    @PRVF.compact.expand_semantic_loop ops.expandValues = @AspisS1NativeCompact.compact.expand_semantic_loop ops := by
  funext iter input out src dst
  delta PRVF.compact.expand_semantic_loop AspisS1NativeCompact.compact.expand_semantic_loop
  simp only [PRVEq.C19_F13.S1NC.expand_semantic_loop.body_i1]
  all_goals rfl

theorem PRVEq.C19_F13.S1NC.expand_semantic_i1 (ops : AspisS1NativeCompact.Ops) :
    @PRVF.compact.expand_semantic ops.expandValues = @AspisS1NativeCompact.compact.expand_semantic ops := by
  funext input out
  delta PRVF.compact.expand_semantic AspisS1NativeCompact.compact.expand_semantic
  simp only [PRVEq.C19_F13.S1NC.COMPACT_SEMANTIC_i1, PRVEq.C19_F13.S1NC.LOGICAL_SEMANTIC_i1, PRVEq.C19_F13.S1NC.SEMANTIC_ROWS_i1, PRVEq.C19_F13.S1NC.expand_semantic_loop_i1]
  all_goals rfl

#print axioms PRVEq.C19_F13.S1NC.SEMANTIC_COMPACT_VALUES_i1
#print axioms PRVEq.C19_F13.S1NC.SEMANTIC_BYTES_i1
#print axioms PRVEq.C19_F13.S1NC.LOGICAL_SEMANTIC_i1
#print axioms PRVEq.C19_F13.S1NC.COMPACT_SEMANTIC_i1
#print axioms PRVEq.C19_F13.S1NC.POINTS_i1
#print axioms PRVEq.C19_F13.S1NC.LANES_i1
#print axioms PRVEq.C19_F13.S1NC.CLAIMS_i1
#print axioms PRVEq.C19_F13.S1NC.row_shape_i1
#print axioms PRVEq.C19_F13.S1NC.compact_row_i1
#print axioms PRVEq.C19_F13.S1NC.SEMANTIC_ROWS_i1
#print axioms PRVEq.C19_F13.S1NC.expand_semantic_loop.body_i1
#print axioms PRVEq.C19_F13.S1NC.expand_semantic_loop_i1
#print axioms PRVEq.C19_F13.S1NC.expand_semantic_i1

end AspisS1NativeCompact
end
end PRVBundle_13
