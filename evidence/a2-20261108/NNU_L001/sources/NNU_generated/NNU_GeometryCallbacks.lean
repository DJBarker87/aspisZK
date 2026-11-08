import NNH_Run5bGeometryReverse
import NNH_Run5bGeometryMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_GeometryCallbacks
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody
open NNH_Run5bGeometrySlots
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

theorem gather :
 verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 (ops m env err r) =
 verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 canonical := by
 rfl

theorem zero :
 verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (ops m env err r) =
 verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool canonical := by
 rfl

theorem prefix (flat : Slice U32) :
 (ops m env err r).op13 flat = canonical.op13 flat := by
 change Port4C_GeometryInverse.prefixCall _ flat = Port4C_GeometryInverse.prefixCall _ flat
 unfold Port4C_GeometryInverse.prefixCall Port4C_GeometryInverse.leaves
 congr 1
 apply Port4C_NativePrefix.Leaves.ext
 · exact funext (fun x => funext (NNH_Run5bGeometrySlots.multiply m env err r x))
 · exact NNH_Run5bGeometrySlots.one m env err r

#print axioms gather
#print axioms zero
#print axioms prefix
end AspisR1.NNU_GeometryCallbacks
end
