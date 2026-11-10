-- PCWT_ binding discharge for the for_range.closure_3 trait-instance keys of Port3_NativeGeometryBody (FnMut/FnOnce TupleSharedM31Bool and call_mut/call_once), route (b).
-- What was bound (PCVF_ k2): the fresh closure_3 text (PCVF_E005, OFF emission, frozen 4bb3b3f) calls the M31 zero constant and the M31 equality; in the gate these are
-- the record slots ops.op6 and ops.op5.  Here the Ext fields are the FRESH FROZEN definitions (M31::ZERO := 0#u32, PCQF_E007; derived PartialEq::eq := ok (self = other), PCQD_E024,
-- crates/aspis-core/src/field.rs 22:22-22:31 and 55:4), and the gate Ops instance ops0 is built from them (all other slots panic).  Statement: fresh x0 = gate ops0.
-- The gate side is the concrete adopted Ops (NFN_NEW_GeometryDictionary.adopted, L187 closure). from_fn := adopted.op0 (core::array::from_fn, an Aeneas Std item with no
-- accepted trust row: HM-D excludes it); the closure_4 keys use it, so they stay conditional on it; the closure_3 keys do not.
import Aeneas
import Port3_NativeGeometryBody
import PRVEq_Port3_closures_k2
import NFN_GeometryPart04
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
noncomputable section

namespace AspisR1.Port3_NativeGeometryBody
namespace PRVFresh_t5

/-- [aspis_core::field::M31::ZERO] (frozen emission PCQF_E007) -/
@[global_simps, irreducible] def aspis_core.field.M31.ZERO : aspis_core.field.M31 := 0#u32

/-- [aspis_core::field::{impl core::cmp::PartialEq<M31> for M31}::eq] (frozen emission PCQD_E024) -/
def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  (self : aspis_core.field.M31) (other : aspis_core.field.M31) : Result Bool := do
  ok (self = other)

def x0 (ff : FromFn) : PRVFresh_k2.Ext where
  from_fn := ff
  zero := ok aspis_core.field.M31.ZERO
  eq := aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq

def x0 : PRVFresh_k2.Ext where
  from_fn := NFN_NEW_GeometryDictionary.adopted.op0
  zero := ok aspis_core.field.M31.ZERO
  eq := aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq

theorem adopted_op5 : NFN_NEW_GeometryDictionary.adopted.op5 = aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq := by
  funext a b
  show NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq a b = _
  unfold NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
  rfl

theorem adopted_op6 : NFN_NEW_GeometryDictionary.adopted.op6 = ok aspis_core.field.M31.ZERO := by
  show ok NEW_GeometryActual.aspis_core.field.M31.ZERO = _
  unfold NEW_GeometryActual.aspis_core.field.M31.ZERO aspis_core.field.M31.ZERO
  rfl

theorem bound : PRVEq.Port3_k2.Bound NFN_NEW_GeometryDictionary.adopted x0 :=
  ⟨fun _ _ _ => rfl, adopted_op5, adopted_op6⟩

end PRVFresh_t5
end AspisR1.Port3_NativeGeometryBody

namespace PRVEq.Port3_t5
open AspisR1.Port3_NativeGeometryBody

theorem closure_3_FnMut_call_mut :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut PRVFresh_t5.x0 =
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut NFN_NEW_GeometryDictionary.adopted :=
  PRVEq.Port3_k2.eq_8 PRVFresh_t5.bound

theorem closure_3_FnOnce_call_once :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once PRVFresh_t5.x0 =
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once NFN_NEW_GeometryDictionary.adopted :=
  PRVEq.Port3_k2.eq_9 PRVFresh_t5.bound

theorem closure_3_FnOnce_inst :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool PRVFresh_t5.x0 =
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool NFN_NEW_GeometryDictionary.adopted :=
  PRVEq.Port3_k2.eq_10 PRVFresh_t5.bound

theorem closure_3_FnMut_inst :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool PRVFresh_t5.x0 =
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool NFN_NEW_GeometryDictionary.adopted :=
  PRVEq.Port3_k2.eq_11 PRVFresh_t5.bound

theorem closure_4_FnMut_call_mut :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut PRVFresh_t5.x0 =
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315.call_mut NFN_NEW_GeometryDictionary.adopted :=
  PRVEq.Port3_k2.eq_4 PRVFresh_t5.bound

theorem closure_4_FnOnce_call_once :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once PRVFresh_t5.x0 =
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315.call_once NFN_NEW_GeometryDictionary.adopted :=
  PRVEq.Port3_k2.eq_5 PRVFresh_t5.bound

theorem closure_4_FnOnce_inst :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 PRVFresh_t5.x0 =
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnOnceTupleUsizeArrayM315 NFN_NEW_GeometryDictionary.adopted :=
  PRVEq.Port3_k2.eq_6 PRVFresh_t5.bound

theorem closure_4_FnMut_inst :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 PRVFresh_t5.x0 =
    verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 NFN_NEW_GeometryDictionary.adopted :=
  PRVEq.Port3_k2.eq_7 PRVFresh_t5.bound

end PRVEq.Port3_t5
#print axioms PRVEq.Port3_t5.closure_3_FnMut_call_mut
#print axioms PRVEq.Port3_t5.closure_3_FnOnce_call_once
#print axioms PRVEq.Port3_t5.closure_3_FnOnce_inst
#print axioms PRVEq.Port3_t5.closure_3_FnMut_inst
#print axioms PRVEq.Port3_t5.closure_4_FnMut_call_mut
#print axioms PRVEq.Port3_t5.closure_4_FnOnce_call_once
#print axioms PRVEq.Port3_t5.closure_4_FnOnce_inst
#print axioms PRVEq.Port3_t5.closure_4_FnMut_inst
