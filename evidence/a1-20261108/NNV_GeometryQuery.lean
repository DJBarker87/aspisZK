import NNV_GeometryQueryForm
import NNV_GeometryEq
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryQuery
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeGeometryBody
open NNH_Run5bGeometrySlots

theorem fibre (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) (u : Usize) :
 NNV_GeometryQueryForm.fibre (ops m env err r) u = NNV_GeometryQueryForm.fibre canonical u :=
 NNV_GeometryIndexPorts.first m env err r u

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (it : core.slice.iter.Iter U32) (q : U32) (zs flat : alloc.vec.Vec U32) :
 NNV_GeometryBranches.query (ops m env err r) it q zs flat =
 NNV_GeometryBranches.query canonical it q zs flat := by
 have zeroTest := NNV_GeometryCallbacks.zero_test (ops m env err r) canonical
  (NNV_GeometrySelectedStd.zero m env err r) (NNV_GeometryEq.source m env err r)
 rw [NNV_GeometryQueryForm.source,NNV_GeometryQueryForm.source]
 simp only [NNV_GeometryQueryForm.normalized,fibre,NNH_Run5bGeometrySlots.point,
  NNH_Run5bGeometrySlots.line,NNH_Run5bGeometrySlots.multiply,NNH_Run5bGeometrySlots.double,
  NNH_Run5bGeometrySlots.one,NNH_Run5bGeometrySlots.subtract,
  NNV_GeometrySelectedStd.any,zeroTest]
#print axioms fibre
#print axioms source
end AspisR1.NNV_GeometryQuery
end
