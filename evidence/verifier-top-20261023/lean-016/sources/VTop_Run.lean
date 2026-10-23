import VTop_Erasure

set_option autoImplicit false
namespace AspisR1.VTop_Run
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace

def ids (log : Log) : List Nat := log.map (fun | .returned op _ => operationId op)

theorem accepted_execution (ops : Ops) {A : Type} (p : Code A) (before : Log) (out : A)
    (accepted : erase ops p = ok out) : ∃ after, run ops p before = ok (out,after) := by
  have erasure := erase_run ops p before
  rw [accepted] at erasure
  cases h : run ops p before with
  | fail e => rw [h] at erasure; cases erasure
  | div => rw [h] at erasure; cases erasure
  | ok result =>
    rw [h] at erasure
    have same := Result.ok.inj erasure
    exact ⟨result.2, by simpa only [same] using h⟩

#print axioms accepted_execution
end AspisR1.VTop_Run
