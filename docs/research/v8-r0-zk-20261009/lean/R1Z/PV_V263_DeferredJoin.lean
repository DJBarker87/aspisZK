import R1Z.PV_V263_WorkerControl
/-! A specific allowed scheduling witness: a spawned worker is deferred until
just before joining its handle. This is not a universal scheduler adequacy
claim. The worker computation itself is retained and executed in the exact
post-world; OS join errors can replace its caught outcome with a panic value.
No runtime answer supplies a vector of successful callback values. -/
set_option autoImplicit false
namespace R1Z.PV_V263_DeferredJoin
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests PV_V263_WorkerControl
open PV_RJ4IDB (Bytes)

structure Task (S A : Type) where
  thread : Nat
  handle : Nat
  action : Q S (Except Bytes A)

def fork {S A : Type} (runtime : Runtime S) (thread : Nat)
    (action : Q S (Except Bytes A)) : Q S (Task S A) :=
  PV_V263_World.bind (spawn runtime thread) fun handle =>
    PV_V263_World.lift (.ok ⟨thread,handle,action⟩)

def join {S A : Type} (runtime : Runtime S) (task : Task S A) : Q S (Except Bytes A) :=
  PV_V263_World.bind task.action fun caught =>
    PV_V263_World.bind (runtime.answer (.join task.thread task.handle)) fun joinError =>
      PV_V263_World.lift (.ok (match joinError with | none => caught | some p => .error p))

def joinAll {S A : Type} (runtime : Runtime S) : List (Task S A) → Q S (List (Except Bytes A))
  | [] => PV_V263_World.lift (.ok [])
  | task::rest => PV_V263_World.bind (join runtime task) fun caught =>
      PV_V263_World.bind (joinAll runtime rest) fun others =>
        PV_V263_World.lift (.ok (caught::others))

theorem granting_join {S A : Type} (encode : {B : Type} → Request B → Bytes)
    (task : Task S A) (w : State S) (caught : Except Bytes A)
    (h : (task.action w).outcome = .returned (.ok caught)) :
    (join (grants encode) task w).outcome = .returned (.ok caught) := by
  simp only [join,PV_V263_World.bind,h,grants,PV_V263_World.lift]

/-- In particular a caught worker panic does not stop the all-handle join loop.
Only after this loop does the source inspect caught results in source order. -/
theorem granting_all {S A : Type} (encode : {B : Type} → Request B → Bytes)
    (tasks : List (Task S A))
    (law : ∀ task, task ∈ tasks → ∀ w,
      ∃ caught, (task.action w).outcome = .returned (.ok caught)) (w : State S) :
    ∃ results, (joinAll (grants encode) tasks w).outcome = .returned (.ok results) := by
  induction tasks generalizing w with
  | nil => exact ⟨[],rfl⟩
  | cons task tasks ih =>
    obtain ⟨caught,hc⟩ := law task (by simp) w
    have hj := granting_join encode task w caught hc
    obtain ⟨others,ho⟩ := ih
      (fun t ht v => law t (by simp only [List.mem_cons]; exact Or.inr ht) v)
      (join (grants encode) task w).state
    exact ⟨caught::others,by simp only [joinAll,PV_V263_World.bind,hj,ho,PV_V263_World.lift]⟩

/-- A small counterexample to early cancellation at the first caught panic:
both actions advance the world, then source-order merge resumes the first.
This is an interpreter check, not a native callback instantiation. -/
def panicTask (thread handle : Nat) (payload : Bytes) : Task Nat (List Unit) :=
  ⟨thread,handle,fun w => ⟨.returned (.ok (.error payload)),{w with base := w.base+1},[]⟩⟩

theorem both_panics_joined (encode : {B : Type} → Request B → Bytes) (w : State Nat) :
    (PV_V263_World.bind
      (joinAll (grants encode) [panicTask 1 0 [2],panicTask 2 1 [17]])
      PV_V263_WorkerControl.merge w).state.base = w.base+2 ∧
    (PV_V263_World.bind
      (joinAll (grants encode) [panicTask 1 0 [2],panicTask 2 1 [17]])
      PV_V263_WorkerControl.merge w).outcome = .fault (.panic [2]) := by
  simp only [joinAll,join,panicTask,PV_V263_World.bind,grants,PV_V263_World.lift,
    PV_V263_WorkerControl.merge,Nat.add_assoc]
  constructor <;> trivial

#print axioms Task
#print axioms fork
#print axioms join
#print axioms joinAll
#print axioms granting_join
#print axioms granting_all
#print axioms panicTask
#print axioms both_panics_joined
end R1Z.PV_V263_DeferredJoin
