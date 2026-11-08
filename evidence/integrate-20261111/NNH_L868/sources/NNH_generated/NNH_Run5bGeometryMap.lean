import NNH_Run5bGeometrySlots
import NNH_Run5bIndexLaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bGeometryMap
open Aeneas Aeneas.Std Result NNH_Run5bGeometrySlots

theorem closure {C : Type} (g : Port3_NativeGeometryBody.Ops C)
 (reply : core.result.Result Usize C) :
 Port4C_GeometryStd.mapError
  (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError g)
  reply () = NNH_Run5bIndexLaw.erase (.ok reply) := by
 cases reply <;> rfl

theorem mapped {C : Type} (g : Port3_NativeGeometryBody.Ops C) (u : Usize) :
 (do let reply ← g.op12 u
     Port4C_GeometryStd.mapError
      (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError g)
      reply ()) = NNH_Run5bIndexLaw.erase (g.op12 u) := by
 unfold NNH_Run5bIndexLaw.erase
 apply bind_congr
 intro reply
 exact closure g reply

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) (u : Usize) :
 (do let reply ← (ops m env err r).op12 u
     Port4C_GeometryStd.mapError
      (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
       (ops m env err r)) reply ()) =
 (do let reply ← canonical.op12 u
     Port4C_GeometryStd.mapError
      (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
       canonical) reply ()) := by
 rw [mapped,mapped]
 exact NNH_Run5bIndexLaw.erase_index err NFN_NEW_GeometryDictionary.err u
#print axioms closure
#print axioms mapped
#print axioms source
end AspisR1.NNH_Run5bGeometryMap
end
