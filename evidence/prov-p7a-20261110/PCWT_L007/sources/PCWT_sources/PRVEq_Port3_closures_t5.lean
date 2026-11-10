-- PCWT_ binding discharge for the for_range.closure_3 trait-instance keys of Port3_NativeGeometryBody (FnMut/FnOnce TupleSharedM31Bool and call_mut/call_once), route (b).
-- What was bound (PCVF_ k2): the fresh closure_3 text (PCVF_E005, OFF emission, frozen 4bb3b3f) calls the M31 zero constant and the M31 equality; in the gate these are
-- the record slots ops.op6 and ops.op5.  Here the Ext fields are the FRESH FROZEN definitions (M31::ZERO := 0#u32, PCQF_E007; derived PartialEq::eq := ok (self = other), PCQD_E024,
-- crates/aspis-core/src/field.rs 22:22-22:31 and 55:4), and the gate Ops instance ops0 is built from them (all other slots panic).  Statement: fresh x0 = gate ops0.
-- NOT closed here: the closure_4 keys use ops.op0 = core::array::from_fn, which has no extraction route and no trust row (HM-D excludes from_fn): from_fn stays a parameter `ff`.
-- The deployed Port3 geometry Ops is left abstract in DrvC_Installation.Configuration; no claim is made about it.
import Aeneas
import Port3_NativeGeometryBody
import PRVEq_Port3_closures_k2
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

abbrev FromFn := ∀ {T : Type} {F : Type} (N : Std.Usize)
  (opsfunctionFnMutFTupleUsizeTInst : core.ops.function.FnMut F Std.Usize T), F → Result (Array T N)

def x0 (ff : FromFn) : PRVFresh_k2.Ext where
  from_fn := ff
  zero := ok aspis_core.field.M31.ZERO
  eq := aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq

/-- every slot panics; only the slots bound below are used by the closure_3 definitions -/
def panicOps (CoreError : Type) : Ops CoreError := by
  constructor <;> intros <;> first | exact fail .panic | exact default

def ops0 (CoreError : Type) (ff : FromFn) : Ops CoreError :=
  { panicOps CoreError with
    op0 := ff
    op5 := aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq
    op6 := ok aspis_core.field.M31.ZERO }

theorem bound (CoreError : Type) (ff : FromFn) : PRVEq.Port3_k2.Bound (ops0 CoreError ff) (x0 ff) :=
  ⟨fun _ _ _ => rfl, rfl, rfl⟩

end PRVFresh_t5
end AspisR1.Port3_NativeGeometryBody

namespace PRVEq.Port3_t5
open AspisR1.Port3_NativeGeometryBody
variable (CoreError : Type) (ff : PRVFresh_t5.FromFn)

theorem closure_3_FnMut_call_mut :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut (PRVFresh_t5.x0 ff) =
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut (PRVFresh_t5.ops0 CoreError ff) :=
  PRVEq.Port3_k2.eq_8 (PRVFresh_t5.bound CoreError ff)

theorem closure_3_FnOnce_call_once :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once (PRVFresh_t5.x0 ff) =
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool.call_once (PRVFresh_t5.ops0 CoreError ff) :=
  PRVEq.Port3_k2.eq_9 (PRVFresh_t5.bound CoreError ff)

theorem closure_3_FnOnce_inst :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool (PRVFresh_t5.x0 ff) =
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnOnceTupleSharedM31Bool (PRVFresh_t5.ops0 CoreError ff) :=
  PRVEq.Port3_k2.eq_10 (PRVFresh_t5.bound CoreError ff)

theorem closure_3_FnMut_inst :
    PRVFresh_k2.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (PRVFresh_t5.x0 ff) =
    verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (PRVFresh_t5.ops0 CoreError ff) :=
  PRVEq.Port3_k2.eq_11 (PRVFresh_t5.bound CoreError ff)

end PRVEq.Port3_t5
#print axioms PRVEq.Port3_t5.closure_3_FnMut_call_mut
#print axioms PRVEq.Port3_t5.closure_3_FnOnce_call_once
#print axioms PRVEq.Port3_t5.closure_3_FnOnce_inst
#print axioms PRVEq.Port3_t5.closure_3_FnMut_inst
