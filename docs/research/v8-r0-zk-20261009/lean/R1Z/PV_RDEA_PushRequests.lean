import R1Z.PV_RDEA_PathBranches
import R1Z.PV_RDEA_PrefixWords
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_PushRequests
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_CapacityEndpoint
open PV_RDEA_PathBranches PV_RDEA_PrefixWords PV_RDEA_AppendRequests

theorem absolute_requests {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (needSep : Bool)
    (b : Buffer U8) (path : List U8) (w : World S F) :
    sizes (sourcePush (PV_RDEA_AppendExecution.append step shape) true needSep b path w).2.history =
      sizes w.history ++ pushWord ⟨b.values.length,b.capacity⟩ path.length true needSep := by
  rw [absolute_push,PV_RDEA_AppendExecution.append_sizes step shape width,absolute_word]
  rfl

theorem no_sep_requests {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1)
    (b : Buffer U8) (path : List U8) (w : World S F) :
    sizes (sourcePush (PV_RDEA_AppendExecution.append step shape) false false b path w).2.history =
      sizes w.history ++ pushWord ⟨b.values.length,b.capacity⟩ path.length false false := by
  rw [relative_no_sep,PV_RDEA_AppendExecution.append_sizes step shape width,relative_no_sep_word]
  rfl

theorem sep_requests_prefix {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1)
    (b : Buffer U8) (path : List U8) (w : World S F) :
    Prefix (sizes (sourcePush (PV_RDEA_AppendExecution.append step shape) false true b path w).2.history)
      (sizes w.history ++ pushWord ⟨b.values.length,b.capacity⟩ path.length false true) := by
  rw [relative_sep,relative_sep_word]
  cases hs : PV_RDEA_AppendExecution.append step shape b [47#u8] w with
  | mk answer after =>
    have hist := PV_RDEA_AppendExecution.append_sizes step shape width b [47#u8] w
    rw [hs] at hist
    dsimp only at hist
    cases answer with
    | error err =>
      simp only [PV_RDEA_StatefulPath.bind]
      rw [hist]
      change Prefix (sizes w.history ++ PV_RDEA_PathSchedule.appendWord
        ⟨b.values.length,b.capacity⟩ 1) _
      exact ⟨PV_RDEA_PathSchedule.appendWord
        (PV_RDEA_PathSchedule.afterAppend ⟨b.values.length,b.capacity⟩ 1) path.length,
        List.append_assoc _ _ _⟩
    | ok next =>
      simp only [PV_RDEA_StatefulPath.bind]
      have hh := PV_RDEA_ExecutionHeaders.append_header step shape b [47#u8] w next
        (congrArg Prod.fst hs)
      rw [PV_RDEA_AppendExecution.append_sizes step shape width,hist]
      simp only [hh.1,hh.2,List.length_append,List.length_cons,List.length_nil,Nat.add_zero]
      unfold PV_RDEA_PathSchedule.appendWord PV_RDEA_PathSchedule.afterAppend
      simp only [List.append_assoc]
      exact PV_RDEA_PrefixWords.refl _

/-- Every possible failure terminates after a prefix of a public size/order
word. Failure's dependence on prior allocator state is retained under rdea-1. -/
theorem push_requests_prefix {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (absolute needSep : Bool)
    (b : Buffer U8) (path : List U8) (w : World S F) :
    Prefix (sizes (sourcePush (PV_RDEA_AppendExecution.append step shape) absolute needSep b path w).2.history)
      (sizes w.history ++ pushWord ⟨b.values.length,b.capacity⟩ path.length absolute needSep) := by
  cases absolute with
  | true => rw [absolute_requests step shape width]; exact PV_RDEA_PrefixWords.refl _
  | false =>
    cases needSep with
    | false => rw [no_sep_requests step shape width]; exact PV_RDEA_PrefixWords.refl _
    | true => exact sep_requests_prefix step shape width b path w

#print axioms absolute_requests
#print axioms no_sep_requests
#print axioms sep_requests_prefix
#print axioms push_requests_prefix
end R1Z.PV_RDEA_PushRequests
