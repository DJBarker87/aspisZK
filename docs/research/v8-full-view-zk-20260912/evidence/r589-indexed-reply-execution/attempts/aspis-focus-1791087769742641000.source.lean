import AspisV8R19.IndependentMeanFixedTape
import AspisV8R19.OracleProgramOps

set_option autoImplicit false
namespace AspisV8R19.R589IndexedReplyExecution
open MemoizedProgramLaw OracleProgramOps IndependentMeanFixedTape
variable {I A O R : Type}

def runIndexed (answer : Nat → A) : Program I A O → Nat → View I A O × Nat
  | .done o, cursor => (([],o),cursor)
  | .ask i next, cursor =>
      let tail := runIndexed answer (next (answer cursor)) (cursor+1)
      (((i,answer cursor)::tail.1.1,tail.1.2),tail.2)

theorem runIndexed_bind (answer : Nat → A) (program : Program I A O)
    (next : O → Program I A R) (cursor : Nat) :
    runIndexed answer (bind program next) cursor =
      let first := runIndexed answer program cursor
      let second := runIndexed answer (next first.1.2) first.2
      ((first.1.1++second.1.1,second.1.2),second.2) := by
  induction program generalizing cursor with
  | done o => rfl
  | ask i k ih => simp only [OracleProgramOps.bind,runIndexed,ih,List.cons_append]

theorem evalTape_runIndexed (program : Program I A O) (fuel : Nat)
    (within : Within program fuel) (tape : Fin fuel → A) (answer : Nat → A)
    (cursor : Nat) (agree : ∀ i : Fin fuel, tape i=answer (cursor+i.val)) :
    evalTape within tape = (runIndexed answer program cursor).1 := by
  induction within generalizing cursor with
  | done o n => rfl
  | ask i next n branches ih =>
      have hfirst : tape 0=answer cursor := by simpa only [Fin.val_zero,Nat.add_zero] using agree 0
      have htail : ∀ j : Fin n, tape j.succ=answer ((cursor+1)+j.val) := by
        intro j
        simpa only [Fin.val_succ,Nat.add_assoc,Nat.add_comm 1 j.val] using agree j.succ
      have hrec := ih (tape 0) (fun j => tape j.succ) (cursor+1) htail
      simp only [evalTape,headTailEquiv,Equiv.coe_fn_mk,runIndexed]
      rw [hrec,hfirst]

#print axioms runIndexed_bind
#print axioms evalTape_runIndexed
end AspisV8R19.R589IndexedReplyExecution
