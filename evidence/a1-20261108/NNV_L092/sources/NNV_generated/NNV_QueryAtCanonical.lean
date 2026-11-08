import NNV_QueryInputPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_QueryAtCanonical
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NNH_Run5bCurrentShape

theorem source (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (proof : Slice U8) (p : LIB_VCarriers.Prepared) (a : LIB_VCarriers.Acc)
 (g : LIB_VCarriers.E29) (geo : LIB_VCarriers.Geo) (pending : LIB_VCarriers.Weights) (stop : Usize) :
 (current m env err r).op7 proof (InstalledPreparation.currentPrepared p)
  (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a)) (NNV_PreparedInputs.scratch g)
  none (Tx1Q_PrefixInstall.unGeometry geo) (Tx1Q_Carriers.unPending pending) stop =
 Tx1Q_Install.result (fun x : Tx1Q_Carriers.S.A × Tx1Q_Carriers.S.B =>
  (Tx1Q_Carriers.unAccumulator x.1,Tx1Q_Carriers.unPending x.2))
 (Port3_NativeQueryBody.verifier.candidate.query_loop
  (Tx1Q_QueryBridge.leaves (NNH_CorrectConfiguration.configuration m env err r).query)
  proof (NFW_PreparedPort.prepared p) (LIBC_VStateCarriers.toAcc a)
  (NFW_PreparedPort.map NFW_PreparedPort.e g) none geo pending stop) := by
 rw [NNV_CurrentQuerySource.source,NNV_PreparedStateTransport.prepared,
  NNV_PreparedStateTransport.scratch,NNV_QueryInputPorts.accumulator,
  NNV_QueryInputPorts.geometry,NNV_QueryInputPorts.pending]
#print axioms source
end AspisR1.NNV_QueryAtCanonical
end
