import NJP_LoopTotal

set_option autoImplicit false
noncomputable section
namespace NJP_LevelsTotal
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel NJP_LoopTotal
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem level_total (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (s : Scratch) (domain : LevelDomain length s) :
 ∃ out, (eval H (level nodes length s)).2=ok out  ∧  LevelProgress length s out := by
 exact rows_total H nodes length s.n s 0 0
   ⟨domain.1,domain.2.1,by omega,by omega,domain.2.2.1,domain.2.2.2⟩
   (by omega) (by omega)

theorem levels_total (H : Request → Digest) (nodes : Nat → U8) (length height : Nat)
    (s : Scratch) (domain : LevelDomain length s) :
 ∃ out, (eval H (levels nodes length height s)).2=ok out  ∧  LevelProgress length s out := by
 induction height generalizing s with
 | zero =>
   exact ⟨.done s,rfl,domain,by omega⟩
 | succ height ih =>
   obtain ⟨out,result,progress⟩ := level_total H nodes length s domain
   let history := (eval H (level nodes length s)).1
   have observed : eval H (level nodes length s)=(history,ok out) := Prod.ext rfl result
   rw [levels,NJP_LoopBind.returned H _ _ history _ observed]
   cases out with
   | stop after => exact ⟨.stop after,rfl,progress⟩
   | done after =>
     obtain ⟨end,returned,valid⟩ := ih after progress.1
     refine ⟨end,returned,?_⟩
     cases end with
     | stop final => exact ⟨valid.1,valid.2.trans_le progress.2⟩
     | done final => exact ⟨valid.1,valid.2.trans progress.2⟩

theorem returning_carrier (H : Request → Digest) (nodes : Nat → U8) (length : Nat)
    (root : Digest) (s : Scratch) (positive : 0<s.n) (size : s.n ≤ 16) (bytes : length ≤ 9216) :
 ∃ (accepted : Bool) (after : Scratch),
   (eval H (run root nodes length s)).2=ok (accepted,after) := by
 have domain : LevelDomain length {s with cursor:=0} := ⟨positive,size,by omega,bytes⟩
 obtain ⟨out,result,_⟩ := levels_total H nodes length 18 {s with cursor:=0} domain
 let history := (eval H (levels nodes length 18 {s with cursor:=0})).1
 have observed : eval H (levels nodes length 18 {s with cursor:=0})=(history,ok out) := Prod.ext rfl result
 unfold run
 rw [NJP_LoopBind.returned H _ _ history _ observed]
 exact ⟨(finish root length out).1,(finish root length out).2,rfl⟩

#print level_total
#print axioms level_total
#print levels_total
#print axioms levels_total
#print returning_carrier
#print axioms returning_carrier
end NJP_LevelsTotal
end
