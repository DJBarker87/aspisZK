import R1Z.PV_RDEA_PushRequests
import R1Z.PV_RDEA_CloneSuccessWord
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_JoinRequests
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint
open PV_RDEA_PathBranches PV_RDEA_PrefixWords

theorem word_decomposition (baseLen pathLen : Nat) (absolute needSep : Bool) :
    PV_RDEA_PathSchedule.joinWord baseLen pathLen absolute needSep =
      cloneWord baseLen ++ pushWord ⟨baseLen,baseLen⟩ pathLen absolute needSep := by
  simp only [PV_RDEA_PathSchedule.joinWord,cloneWord,pushWord,List.append_assoc]

/-- Concrete clone + two native byte-appends. Every early failure preserves
its world and terminates on a prefix of the public request-size/order word. -/
theorem join_requests_prefix {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (absolute needSep : Bool)
    (base path : List U8) (w : World S F) :
    Prefix (sizes (sourceJoin (PV_RDEA_CloneExecution.clone step shape address)
      (PV_RDEA_AppendExecution.append step shape) absolute needSep base path w).2.history)
      (sizes w.history ++ PV_RDEA_PathSchedule.joinWord base.length path.length absolute needSep) := by
  rw [word_decomposition]
  unfold sourceJoin
  cases hc : PV_RDEA_CloneExecution.clone step shape address base w with
  | mk response after =>
    cases response with
    | error err =>
      simp only [PV_RDEA_StatefulPath.bind]
      have hp := PV_RDEA_ClonePrefix.clone_requests_prefix step shape width address base w
      rw [hc] at hp
      dsimp only at hp
      simpa only [List.append_assoc] using right _ _
        (pushWord ⟨base.length,base.length⟩ path.length absolute needSep) hp
    | ok b =>
      simp only [PV_RDEA_StatefulPath.bind]
      have hb := PV_RDEA_ExecutionHeaders.clone_header step shape address base w b (congrArg Prod.fst hc)
      have hist := PV_RDEA_CloneSuccessWord.clone_word_success step shape width address base w b (congrArg Prod.fst hc)
      rw [hc] at hist
      dsimp only at hist
      have hp := PV_RDEA_PushRequests.push_requests_prefix step shape width absolute needSep b path after
      rw [hb.1,hb.2,hist] at hp
      simpa only [List.append_assoc] using hp

#print axioms word_decomposition
#print axioms join_requests_prefix
end R1Z.PV_RDEA_JoinRequests
