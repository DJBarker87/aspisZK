import NNU_GeometryBody
import NNU_GeometryStdSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_GeometryTraversal
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody NNH_Run5bGeometrySlots

theorem selected_step (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (start : Usize) (iter : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32) :
 verifier.QueryGeometry.for_range_loop0.body (ops m env err r) start iter zs flat =
 verifier.QueryGeometry.for_range_loop0.body canonical start iter zs flat := by
 have std := NNU_GeometryStdSlots.slots
  (NNH_CorrectConfiguration.configuration m env err r).geometry
  (NFN_NEB_ActualGeometryModel.install NFN_NEW_GeometryRawInterface.ops NFN_NEW_GeometryDictionary.err)
 exact NNU_GeometryBody.step _ _
  (NNU_GeometryStdSlots.map_error _) (NNU_GeometryStdSlots.map_error _)
  std.1 std.2.1 std.2.2.1 std.2.2.2.1
  (NNH_Run5bGeometrySlots.one m env err r)
  (funext (fun x=>funext (NNH_Run5bGeometrySlots.subtract m env err r x)))
  (funext (fun x=>funext (NNH_Run5bGeometrySlots.multiply m env err r x)))
  (funext (NNH_Run5bGeometrySlots.double m env err r))
  (funext (NNH_Run5bGeometrySlots.inverse m env err r))
  (funext (NNU_GeometrySelected.prefixCall m env err r))
  (funext (NNH_Run5bGeometrySlots.line m env err r))
  (funext (NNH_Run5bGeometrySlots.point m env err r))
  std.2.2.2.2 (NNU_GeometrySelected.gather m env err r)
  (NNU_GeometrySelected.zero m env err r)
  (NNH_Run5bIndexLaw.erase_index err NFN_NEW_GeometryDictionary.err) start iter zs flat

theorem selected_loop (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (iter : core.slice.iter.Iter U32) (start : Usize) (zs flat : alloc.vec.Vec U32) :
 verifier.QueryGeometry.for_range_loop0 (ops m env err r) iter start zs flat =
 verifier.QueryGeometry.for_range_loop0 canonical iter start zs flat := by
 unfold verifier.QueryGeometry.for_range_loop0
 apply congrArg (fun f=>Aeneas.Std.loop f (iter,zs,flat))
 funext state
 exact selected_step m env err r start state.1 state.2.1 state.2.2

#print axioms selected_step
#print axioms selected_loop
end AspisR1.NNU_GeometryTraversal
end
