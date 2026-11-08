import NNV_GeometryTerminal
import NNV_GeometryQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_GeometryBody
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeGeometryBody NNH_Run5bGeometrySlots

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (start : Usize) (it : core.slice.iter.Iter U32) (zs flat : alloc.vec.Vec U32) :
 verifier.QueryGeometry.for_range_loop0.body (ops m env err r) start it zs flat =
 verifier.QueryGeometry.for_range_loop0.body canonical start it zs flat := by
 rw [NNV_GeometryBranches.body,NNV_GeometryBranches.body]
 apply bind_congr
 rintro ⟨o,it1⟩
 cases o with
 | none => exact NNV_GeometryTerminal.source m env err r start zs flat
 | some q => exact NNV_GeometryQuery.source m env err r it1 q zs flat
#print axioms source
end AspisR1.NNV_GeometryBody
end
