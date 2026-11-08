import NNV_GeometryBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryOuter
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeGeometryBody NNH_Run5bGeometrySlots
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

theorem loop (start : Usize) (it : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32) :
 verifier.QueryGeometry.for_range_loop0 (ops m env err r) it start zs flat =
 verifier.QueryGeometry.for_range_loop0 canonical it start zs flat := by
 unfold verifier.QueryGeometry.for_range_loop0
 apply congrArg (fun f => Aeneas.Std.loop f (it,zs,flat))
 funext state
 exact NNV_GeometryBody.source m env err r start state.1 state.2.1 state.2.2

theorem source (queries : Array U32 22#usize) (start stop : Usize) :
 verifier.QueryGeometry.for_range (ops m env err r) queries start stop =
 verifier.QueryGeometry.for_range canonical queries start stop := by
 simp only [verifier.QueryGeometry.for_range,loop]

theorem stage (queries : Array U32 22#usize) (start stop : Usize) :
 Port3_GeometryStage.geometry (ops m env err r) queries start stop =
 Port3_GeometryStage.geometry canonical queries start stop :=
 congrArg Port3_QueryInstall.result (source m env err r queries start stop)
#print axioms loop
#print axioms source
#print axioms stage
end AspisR1.NNV_GeometryOuter
end
