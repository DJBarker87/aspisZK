import R1Z.PV_RDEA_ExecutionHeaders
open Aeneas Aeneas.Std
namespace R1Z.PV_RDEA_PathBranches
open PV_RDB1_V183_ReserveWorld PV_RDEA_StatefulPath

theorem absolute_push {S F : Type}
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (needSep : Bool) (b : Buffer U8) (path : List U8) (w : World S F) :
    sourcePush append true needSep b path w = append (PV_RDB1_V178.cleared b) path w := by
  simp [sourcePush,PV_RDEA_StatefulPath.bind,clear,PV_RDB1_V178.byte_drops]

theorem relative_no_sep {S F : Type}
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (b : Buffer U8) (path : List U8) (w : World S F) :
    sourcePush append false false b path w=append b path w := rfl

theorem relative_sep {S F : Type}
    (append : Buffer U8 → List U8 → World S F → Outcome (Buffer U8) S F)
    (b : Buffer U8) (path : List U8) (w : World S F) :
    sourcePush append false true b path w=
      PV_RDEA_StatefulPath.bind (append b [47#u8] w) (fun b w => append b path w) := rfl

def pushWord (h : PV_RDEA_PathSchedule.Header) (pathLen : Nat) (absolute needSep : Bool) :
    List (Nat × Nat × Nat) :=
  let cleared := if absolute then {h with len:=0} else h
  let sep := !absolute && needSep
  let sepWord := if sep then PV_RDEA_PathSchedule.appendWord cleared 1 else []
  let afterSep := if sep then PV_RDEA_PathSchedule.afterAppend cleared 1 else cleared
  sepWord ++ PV_RDEA_PathSchedule.appendWord afterSep pathLen

theorem absolute_word (h : PV_RDEA_PathSchedule.Header) (pathLen : Nat) (needSep : Bool) :
    pushWord h pathLen true needSep=PV_RDEA_PathSchedule.appendWord ⟨0,h.cap⟩ pathLen := by
  simp [pushWord]

theorem relative_no_sep_word (h : PV_RDEA_PathSchedule.Header) (pathLen : Nat) :
    pushWord h pathLen false false=PV_RDEA_PathSchedule.appendWord h pathLen := rfl

theorem relative_sep_word (h : PV_RDEA_PathSchedule.Header) (pathLen : Nat) :
    pushWord h pathLen false true=PV_RDEA_PathSchedule.appendWord h 1 ++
      PV_RDEA_PathSchedule.appendWord (PV_RDEA_PathSchedule.afterAppend h 1) pathLen := rfl

#print axioms absolute_push
#print axioms relative_no_sep
#print axioms relative_sep
#print axioms absolute_word
#print axioms relative_no_sep_word
#print axioms relative_sep_word
end R1Z.PV_RDEA_PathBranches
