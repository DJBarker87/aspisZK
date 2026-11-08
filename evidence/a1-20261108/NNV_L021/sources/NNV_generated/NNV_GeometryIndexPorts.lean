import NNH_Run5bGeometryMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryIndexPorts
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody
open verifier.QueryGeometry.for_range NNH_Run5bGeometrySlots
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
theorem first (u : Usize) :
 (do let value ← (ops m env err r).op12 u
     (ops m env err r).op2 (closure.Insts.CoreOpsFunctionFnOnceTupleErrorError (ops m env err r)) value ()) =
 (do let value ← canonical.op12 u
     canonical.op2 (closure.Insts.CoreOpsFunctionFnOnceTupleErrorError canonical) value ()) :=
 NNH_Run5bGeometryMap.source m env err r u

theorem second (u : Usize) :
 (do let value ← (ops m env err r).op12 u
     (ops m env err r).op2 (closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError (ops m env err r)) value ()) =
 (do let value ← canonical.op12 u
     canonical.op2 (closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError canonical) value ()) :=
 NNH_Run5bGeometryMap.source m env err r u

theorem third (u : Usize) :
 (do let value ← (ops m env err r).op12 u
     (ops m env err r).op2 (closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError (ops m env err r)) value ()) =
 (do let value ← canonical.op12 u
     canonical.op2 (closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError canonical) value ()) :=
 NNH_Run5bGeometryMap.source m env err r u
#print axioms first
#print axioms second
#print axioms third
end AspisR1.NNV_GeometryIndexPorts
end
