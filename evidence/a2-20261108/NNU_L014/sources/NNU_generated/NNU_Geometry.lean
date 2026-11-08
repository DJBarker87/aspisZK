import NNU_GeometryTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_Geometry
open Aeneas Aeneas.Std Result Port3_NativeGeometryBody NNH_Run5bGeometrySlots

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (queries : Array U32 22#usize) (start finish : Usize) :
 (NNH_Tx2SlotTransport.stage m env err r).op11 queries start finish =
 NJC_ClosedCalls.geometry queries start finish := by
 rw [NNH_Tx2SlotTransport.geometry_slot,NJC_ClosedCalls.geometry_clause]
 unfold Port3_GeometryStage.geometry verifier.QueryGeometry.for_range
 simp only [NNU_GeometryTraversal.selected_loop]

theorem returned : NNH_Tx2OpenSlots.geometry := by
 intro m env err r queries start finish out accepted
 rw [source m env err r queries start finish]
 exact accepted
#print axioms source
#print axioms returned
end AspisR1.NNU_Geometry
end
