import R1Z.PV_RDEA_JoinRequests
import R1Z.PV_RDEA_PushSuccessRequests
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_JoinSuccessRequests
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint

theorem success_word {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (absolute needSep : Bool)
    (base path : List U8) (w : World S F) (out : Buffer U8)
    (success : (sourceJoin (PV_RDEA_CloneExecution.clone step shape address)
      (PV_RDEA_AppendExecution.append step shape) absolute needSep base path w).1=.ok out) :
    sizes (sourceJoin (PV_RDEA_CloneExecution.clone step shape address)
      (PV_RDEA_AppendExecution.append step shape) absolute needSep base path w).2.history =
      sizes w.history ++ PV_RDEA_PathSchedule.joinWord base.length path.length absolute needSep := by
  rw [PV_RDEA_JoinRequests.word_decomposition]
  unfold sourceJoin at success ⊢
  cases hc : PV_RDEA_CloneExecution.clone step shape address base w with
  | mk response after =>
    rw [hc] at success
    cases response with
    | error err =>
      simp only [PV_RDEA_StatefulPath.bind] at success
      cases success
    | ok b =>
      simp only [PV_RDEA_StatefulPath.bind] at success ⊢
      have hb := PV_RDEA_ExecutionHeaders.clone_header step shape address base w b (congrArg Prod.fst hc)
      have hist := PV_RDEA_CloneSuccessWord.clone_word_success step shape width address base w b (congrArg Prod.fst hc)
      rw [hc] at hist
      dsimp only at hist
      rw [PV_RDEA_PushSuccessRequests.success_word step shape width absolute needSep b path after out success,
        hb.1,hb.2,hist,List.append_assoc]

#print axioms success_word
end R1Z.PV_RDEA_JoinSuccessRequests
