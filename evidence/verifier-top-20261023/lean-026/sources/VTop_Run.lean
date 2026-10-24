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
    exact ⟨result.2, congrArg Result.ok (Prod.ext same rfl)⟩

theorem run_bind (ops : Ops) {A B : Type} (p : Code A) (k : A → Code B) (before : Log) :
    run ops (p >>= k) before = thenResult (run ops p before) (fun out => run ops (k out.1) out.2) := by
  induction p generalizing before with
  | done a => rfl
  | step r c ih =>
    cases r with
    | fail e => rfl
    | div => rfl
    | ok b => exact ih b before
  | call op c ih =>
    cases h : invoke ops op with
    | fail e => simp only [Bind.bind,VTop_Trace.bind,run,h,thenResult]
    | div => simp only [Bind.bind,VTop_Trace.bind,run,h,thenResult]
    | ok b => simpa only [Bind.bind,VTop_Trace.bind,run,h,thenResult] using ih b (before ++ [.returned op b])

theorem run_perform (ops : Ops) {A : Type} (op : Call A) (before : Log) :
    run ops (perform op) before = thenResult (invoke ops op) (fun out => ok (out,before ++ [.returned op out])) := rfl

theorem run_lift (ops : Ops) {A : Type} (r : Result A) (before : Log) :
    run ops (monadLift r : Code A) before = thenResult r (fun out => ok (out,before)) := rfl

theorem run_pure (ops : Ops) {A : Type} (a : A) (before : Log) :
    run ops (pure a) before = ok (a,before) := rfl

universe u v w
theorem thenResult_assoc {A : Type u} {B : Type v} {C : Type w}
    (r : Result A) (f : A → Result B) (g : B → Result C) :
    thenResult (thenResult r f) g = thenResult r (fun a => thenResult (f a) g) := by
  cases r <;> rfl

#print axioms accepted_execution
#print axioms run_bind
#print axioms run_perform
#print axioms run_lift
#print axioms run_pure
#print axioms thenResult_assoc
end AspisR1.VTop_Run
