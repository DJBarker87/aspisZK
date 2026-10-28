import R1Z.PV_RDEA_JoinSuccessRequests
import R1Z.PV_RDEA_PushValues
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_JoinValues
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath

theorem success_value {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (address : Nat) (absolute needSep : Bool)
    (base path : List U8) (w : World S F) (out : Buffer U8)
    (success : (sourceJoin (PV_RDEA_CloneExecution.clone step shape address)
      (PV_RDEA_AppendExecution.append step shape) absolute needSep base path w).1=.ok out) :
    out.values=PV_RDEA_PushValues.value base path absolute needSep := by
  unfold sourceJoin at success
  cases hc : PV_RDEA_CloneExecution.clone step shape address base w with
  | mk response after =>
    rw [hc] at success
    cases response with
    | error err => simp only [PV_RDEA_StatefulPath.bind] at success; cases success
    | ok b =>
      simp only [PV_RDEA_StatefulPath.bind] at success
      have hb := PV_RDEA_ExecutionHeaders.clone_header step shape address base w b (congrArg Prod.fst hc)
      rw [PV_RDEA_PushValues.success_value step shape absolute needSep b path after out success,hb.1]

#print axioms success_value
end R1Z.PV_RDEA_JoinValues
