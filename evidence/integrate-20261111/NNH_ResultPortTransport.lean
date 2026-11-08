import NNH_Tx2SlotTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_ResultPortTransport
open Aeneas Aeneas.Std Result

theorem port {A : Type} (r : Result (core.result.Result A NHT_ResultPort.SourceError)) :
 Port3_QueryInstall.result r = NHT_ResultPort.action r := by
 cases r with
 | fail e => rfl
 | div => rfl
 | ok reply => cases reply with
  | Ok value => rfl
  | Err error => cases error <;> rfl

theorem finish (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (v : VTop_Stages.verifier.View) (p : VTop_Stages.verifier.Prepared)
 (a : VTop_Stages.verifier.Accumulator) :
 (NNH_Tx2SlotTransport.stage missing env err reserve).op19 v p a none =
 NLB_Parent.finish reserve v p a none := by
 rw [NNH_Tx2SlotTransport.finish_slot]
 exact port _
#print axioms port
#print axioms finish
end AspisR1.NNH_ResultPortTransport
end
