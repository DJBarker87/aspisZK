import R1Z.PV_RDEA_PushSuccessRequests
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_PushValues
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath PV_RDEA_PathBranches

def value (base path : List U8) (absolute needSep : Bool) : List U8 :=
  if absolute then path else if needSep then (base++[47#u8])++path else base++path

theorem absolute_value {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (needSep : Bool) (b : Buffer U8)
    (path : List U8) (w : World S F) (out : Buffer U8)
    (success : (sourcePush (PV_RDEA_AppendExecution.append step shape) true needSep b path w).1=.ok out) :
    out.values=path := by
  rw [absolute_push] at success
  have h := PV_RDEA_ExecutionHeaders.append_header step shape (PV_RDB1_V178.cleared b) path w out success
  exact h.1

theorem no_sep_value {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (path : List U8) (w : World S F) (out : Buffer U8)
    (success : (sourcePush (PV_RDEA_AppendExecution.append step shape) false false b path w).1=.ok out) :
    out.values=b.values++path := by
  rw [relative_no_sep] at success
  exact (PV_RDEA_ExecutionHeaders.append_header step shape b path w out success).1

theorem separator_value {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (b : Buffer U8) (path : List U8) (w : World S F) (out : Buffer U8)
    (success : (sourcePush (PV_RDEA_AppendExecution.append step shape) false true b path w).1=.ok out) :
    out.values=(b.values++[47#u8])++path := by
  rw [relative_sep] at success
  cases hs : PV_RDEA_AppendExecution.append step shape b [47#u8] w with
  | mk response after =>
    rw [hs] at success
    cases response with
    | error err => simp only [PV_RDEA_StatefulPath.bind] at success; cases success
    | ok next =>
      simp only [PV_RDEA_StatefulPath.bind] at success
      have first := PV_RDEA_ExecutionHeaders.append_header step shape b [47#u8] w next (congrArg Prod.fst hs)
      have last := PV_RDEA_ExecutionHeaders.append_header step shape next path after out success
      rw [last.1,first.1]

theorem success_value {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (absolute needSep : Bool) (b : Buffer U8)
    (path : List U8) (w : World S F) (out : Buffer U8)
    (success : (sourcePush (PV_RDEA_AppendExecution.append step shape) absolute needSep b path w).1=.ok out) :
    out.values=value b.values path absolute needSep := by
  cases absolute with
  | true => exact absolute_value step shape needSep b path w out success
  | false =>
    cases needSep with
    | false => exact no_sep_value step shape b path w out success
    | true => exact separator_value step shape b path w out success

#print axioms absolute_value
#print axioms no_sep_value
#print axioms separator_value
#print axioms success_value
end R1Z.PV_RDEA_PushValues
