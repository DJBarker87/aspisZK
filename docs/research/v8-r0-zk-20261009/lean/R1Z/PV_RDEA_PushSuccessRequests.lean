import R1Z.PV_RDEA_PushRequests
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_PushSuccessRequests
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint
open PV_RDEA_PathBranches PV_RDEA_AppendRequests

theorem separator_success_word {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (b : Buffer U8)
    (path : List U8) (w : World S F) (out : Buffer U8)
    (success : (sourcePush (PV_RDEA_AppendExecution.append step shape) false true b path w).1=.ok out) :
    sizes (sourcePush (PV_RDEA_AppendExecution.append step shape) false true b path w).2.history =
      sizes w.history ++ pushWord ⟨b.values.length,b.capacity⟩ path.length false true := by
  rw [relative_sep,relative_sep_word]
  rw [relative_sep] at success
  cases hs : PV_RDEA_AppendExecution.append step shape b [47#u8] w with
  | mk answer after =>
    rw [hs] at success
    have hist := PV_RDEA_AppendExecution.append_sizes step shape width b [47#u8] w
    rw [hs] at hist
    dsimp only at hist
    cases answer with
    | error err =>
      simp only [PV_RDEA_StatefulPath.bind] at success
      cases success
    | ok next =>
      simp only [PV_RDEA_StatefulPath.bind]
      have hh := PV_RDEA_ExecutionHeaders.append_header step shape b [47#u8] w next
        (congrArg Prod.fst hs)
      rw [PV_RDEA_AppendExecution.append_sizes step shape width,hist]
      simp only [hh.1,hh.2,List.length_append,List.length_cons,List.length_nil]
      unfold PV_RDEA_PathSchedule.appendWord PV_RDEA_PathSchedule.afterAppend
      simp only [List.append_assoc]

theorem success_word {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (absolute needSep : Bool)
    (b : Buffer U8) (path : List U8) (w : World S F) (out : Buffer U8)
    (success : (sourcePush (PV_RDEA_AppendExecution.append step shape) absolute needSep b path w).1=.ok out) :
    sizes (sourcePush (PV_RDEA_AppendExecution.append step shape) absolute needSep b path w).2.history =
      sizes w.history ++ pushWord ⟨b.values.length,b.capacity⟩ path.length absolute needSep := by
  cases absolute with
  | true => exact PV_RDEA_PushRequests.absolute_requests step shape width needSep b path w
  | false =>
    cases needSep with
    | false => exact PV_RDEA_PushRequests.no_sep_requests step shape width b path w
    | true => exact separator_success_word step shape width b path w out success

#print axioms separator_success_word
#print axioms success_word
end R1Z.PV_RDEA_PushSuccessRequests
