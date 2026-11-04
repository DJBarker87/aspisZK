import NFA_Iterator
set_option autoImplicit false
namespace AspisR1.NFA_CursorRelation
open Aeneas Aeneas.Std Result
/-- Exact scalar fields observed by K012–K017. This is a compiler-pinned
representation packet, not a portable ABI assertion. -/
structure Native where
  start : Nat
  remaining : Nat
  stepMinusOne : Nat
  first : Bool

def step (s : Native) : Option Nat × Native :=
 if s.remaining>0 then (some s.start,{s with start:=s.start+s.stepMinusOne+1,remaining:=s.remaining-1})
 else (none,s)
structure Related (n : Nat) (s : Native) (iter : NFA_Iterator.Iter) : Prop where
  bounded : n≤7
  start : s.start=4*n
  remaining : s.remaining=7-n
  stride : s.stepMinusOne=3
  modelStart : iter.iter.start.val=min (4*n) 26
  modelEnd : iter.iter.end.val=26
  modelStride : iter.step_by.val=4

theorem initial : Related 0 ⟨0,7,3,true⟩ (NFA_Iterator.value 0) := by
  constructor <;> first | omega | rfl
/-- Every complete arbitrary-prestate native scalar step has the SAME reply as
cohort StepBy and preserves the representation relation, including terminal28
versus model26. The Bool is unrestricted and unchanged by the native law. -/
theorem association (n : Nat) (s : Native) (iter : NFA_Iterator.Iter)
    (relation : Related n s iter) :
    ∃ reply next,
      core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter=ok (reply,next) ∧
      (step s).1=reply.map (fun x=>x.val) ∧ Related (min (n+1) 7) (step s).2 next := by
  rcases relation with ⟨bounded,start,remaining,stride,modelStart,modelEnd,modelStride⟩
  by_cases active : n<7
  · have inside : iter.iter.start.val < iter.iter.end.val := by omega
    have positive : 0<s.remaining := by omega
    obtain ⟨next,run,advance,finish,stride'⟩:=NFA_Iterator.next iter modelStride inside
    refine ⟨some iter.iter.start,next,run,?_,?_⟩
    · simp only [step,if_pos positive,Option.map_some]
      apply congrArg some
      omega
    · have cap : min (n+1) 7=n+1:=Nat.min_eq_left (by omega)
      rw [cap]
      simp only [step,if_pos positive]
      constructor
      · omega
      · dsimp only;omega
      · dsimp only;omega
      · exact stride
      · rw [advance,modelStart,modelEnd];omega
      · simpa only [finish] using modelEnd
      · exact stride'
  · have terminal : n=7 := by omega
    have exhausted : ¬0<s.remaining := by omega
    have halt : iter.iter.end.val ≤ iter.iter.start.val := by omega
    refine ⟨none,iter,NFA_Iterator.stopped iter halt,?_,?_⟩
    · simp only [step,if_neg exhausted,Option.map_none]
    · simp only [step,if_neg exhausted]
      have cap : min (n+1) 7=n := by omega
      rw [cap]
      exact ⟨bounded,start,remaining,stride,modelStart,modelEnd,modelStride⟩
#print axioms initial
#print axioms association
end AspisR1.NFA_CursorRelation
