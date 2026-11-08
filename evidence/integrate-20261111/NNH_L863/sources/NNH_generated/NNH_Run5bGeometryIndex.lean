import NNH_Run5bGeometrySlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bGeometryIndex
open Aeneas Aeneas.Std Result NNH_Run5bGeometrySlots
variable (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

theorem admitted (u : Usize) (bound : u.val < 262144) :
 (ops m env err r).op12 u = .ok (.Ok u) := by
 change SAQ_Constructor.fibre err u = .ok (.Ok u)
 unfold SAQ_Constructor.fibre
 rw [if_pos bound]

theorem canonical_admitted (u : Usize) (bound : u.val < 262144) :
 canonical.op12 u = .ok (.Ok u) :=
 NFN_NEB_GeometryIndices.admitted _ u bound

/-- Compare the mapped error class, preserving every successful index. -/
theorem mapped (u : Usize) :
 (do let x ← (ops m env err r).op12 u
     Port4C_GeometryStd.mapError
      (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
       (ops m env err r)) x ()) =
 (do let x ← canonical.op12 u
     Port4C_GeometryStd.mapError
      (Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError
       canonical) x ()) := by
 change (do let x ← SAQ_Constructor.fibre err u
            Port4C_GeometryStd.mapError _ x ()) =
        (do let x ← NFN_NEB_GeometryIndices.indexPort NFN_NEW_GeometryDictionary.err u
            Port4C_GeometryStd.mapError _ x ())
 simp only [SAQ_Constructor.fibre,NFN_NEB_GeometryIndices.indexPort,NEA_Reference.fibre_new_ref]
 split <;> rfl
#print axioms admitted
#print axioms canonical_admitted
#print axioms mapped
end AspisR1.NNH_Run5bGeometryIndex
end
