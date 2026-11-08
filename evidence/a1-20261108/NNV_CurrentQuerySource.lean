import NNV_PreparedStateTransport
import NNH_Run5bCurrentShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_CurrentQuerySource
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open NNH_Run5bCurrentShape

theorem slot (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geo : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (stop : Usize) :
 (current m env err r).op7 proof p a g none geo pending stop =
 Tx1Q_Install.query (Tx1Q_QueryBridge.leaves (NNH_CorrectConfiguration.configuration m env err r).query)
  proof p a g none geo pending stop := rfl

/-- Original Prepared and scratch reach the native query call unchanged under
nominal carriers. This does not yet identify the native query dictionary
with the canonical library's fixed query evaluator. -/
theorem prepared_input (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) :
 (Tx1Q_Carriers.prepared (InstalledPreparation.currentPrepared p),
  Tx1Q_Carriers.arr Tx1Q_Carriers.e (NNV_PreparedInputs.scratch g)) =
 (NFW_PreparedPort.prepared p,NFW_PreparedPort.map NFW_PreparedPort.e g) :=
 Prod.ext (NNV_PreparedStateTransport.prepared p) (NNV_PreparedStateTransport.scratch g)
theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geo : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (stop : Usize) :
 (current m env err r).op7 proof p a g none geo pending stop =
 Tx1Q_Install.result (fun x : Tx1Q_Carriers.S.A × Tx1Q_Carriers.S.B =>
  (Tx1Q_Carriers.unAccumulator x.1,Tx1Q_Carriers.unPending x.2))
 (Port3_NativeQueryBody.verifier.candidate.query_loop
  (Tx1Q_QueryBridge.leaves (NNH_CorrectConfiguration.configuration m env err r).query)
  proof (Tx1Q_Carriers.prepared p) (Tx1Q_Carriers.accumulator a)
  (Tx1Q_Carriers.arr Tx1Q_Carriers.e g) none (Tx1Q_Carriers.geometry geo)
  (Tx1Q_Carriers.pending pending) stop) := by
 rw [slot]
 exact Tx1Q_QueryBridge.query_body _ proof p a g none geo pending stop
#print axioms source
#print axioms slot
#print axioms prepared_input
end AspisR1.NNV_CurrentQuerySource
end
