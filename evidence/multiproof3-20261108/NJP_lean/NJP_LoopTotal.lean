import NJP_LoopBind
import NJP_RowInvariant

set_option autoImplicit false
noncomputable section
namespace NJP_LoopTotal
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel NJP_RowInvariant
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def LevelDomain (length : Nat) (s : Scratch) : Prop :=
 0<s.n  ∧  s.n ≤ 16  ∧  s.cursor ≤ length  ∧  length ≤ 9216

def LevelProgress (length : Nat) (before : Scratch) : Level → Prop
 | .stop after => LevelDomain length after  ∧  after.n=before.n
 | .done after => LevelDomain length after  ∧  after.n ≤ before.n

theorem rows_total (H : Request → Digest) (nodes : Nat → U8) (length fuel : Nat)
    (s : Scratch) (i w : Nat) (domain : Domain length s i w)
    (budget : s.n - i ≤ fuel) (nonempty : 0 < i → 0 < w) :
 ∃ out, (eval H (rows nodes length fuel s i w)).2=ok out  ∧  LevelProgress length s out := by
 induction fuel generalizing s i w with
 | zero =>
   have halted : s.n ≤ i := by obtain ⟨_,_,read,_,_,_⟩ := domain;omega
   have same : i=s.n := by obtain ⟨_,_,read,_,_,_⟩ := domain;omega
   have positive : 0 < w := nonempty (by obtain ⟨positive,_,_,_,_,_⟩ := domain;omega)
   obtain ⟨_,size,_,writeBound,cursorBound,byteBound⟩ := domain
   refine ⟨.done {s with n:=w},?_,?_⟩
   · simp only [rows,if_pos halted,eval]
   · change (0 < w ∧ w ≤ 16 ∧ s.cursor ≤ length ∧ length ≤ 9216) ∧ w ≤ s.n
     exact ⟨⟨positive,by omega,cursorBound,byteBound⟩,by omega⟩
 | succ fuel ih =>
   by_cases halted : s.n ≤ i
   · have same : i=s.n := by obtain ⟨_,_,read,_,_,_⟩ := domain;omega
     have positive : 0 < w := nonempty (by obtain ⟨positive,_,_,_,_,_⟩ := domain;omega)
     obtain ⟨_,size,_,writeBound,cursorBound,byteBound⟩ := domain
     refine ⟨.done {s with n:=w},?_,?_⟩
     · simp only [rows,if_pos halted,eval]
     · change (0 < w ∧ w ≤ 16 ∧ s.cursor ≤ length ∧ length ≤ 9216) ∧ w ≤ s.n
       exact ⟨⟨positive,by omega,cursorBound,byteBound⟩,by omega⟩
   · have active : i < s.n := by omega
     obtain ⟨out,result,progress⟩ := node_progress H nodes length s i w domain active
     let history := (eval H (node nodes length s i w)).1
     have observed : eval H (node nodes length s i w)=(history,ok out) := Prod.ext rfl result
     rw [rows,if_neg halted,NJP_LoopBind.returned H _ _ history _ observed]
     cases out with
     | stop after =>
       have same : after=s := progress
       subst after
       refine ⟨.stop s,?_,?_⟩
       · simp only [eval,List.append_nil]
       · exact ⟨⟨domain.1,domain.2.1,domain.2.2.2.2.1,domain.2.2.2.2.2⟩,rfl⟩
     | next after ni nw =>
       obtain ⟨sameN,nextDomain,advance,writeAdvance⟩ := progress
       have remaining : after.n-ni ≤ fuel := by rw [sameN];omega
       have prefix_nonempty : 0 < ni → 0 < nw := by intro _;omega
       obtain ⟨final,returned,valid⟩ := ih after ni nw nextDomain remaining prefix_nonempty
       refine ⟨final,returned,?_⟩
       cases final <;> simpa only [LevelProgress,sameN] using valid

#print rows_total
#print axioms rows_total
end NJP_LoopTotal
end
