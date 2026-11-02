import R1Z.PV_V263_WorkerRequests
/-! Source control combinators. No worker/callback success is postulated.
Traversal executes the actual supplied computation at each index/post-world.
Caught panics are VALUES; abort, finite-fuel exhaustion and source divergence
remain distinct and do not run ordinary return-time destructors. -/
set_option autoImplicit false
namespace R1Z.PV_V263_WorkerControl
open Aeneas Aeneas.Std PV_V263_World PV_V263_WorkerRequests
open PV_RJ4IDB (Bytes)

inductive Profile where
  | unwind
  | abort
 deriving DecidableEq

def catchPanic {S A : Type} (profile : Profile) (action : Q S A) : Q S (Except Bytes A) := fun w =>
  let r := action w
  match r.outcome with
  | .returned (.ok a) => ⟨.returned (.ok (.ok a)),r.state,r.events⟩
  | .returned (.fail e) => ⟨.returned (.fail e),r.state,r.events⟩
  | .returned .div => ⟨.returned .div,r.state,r.events⟩
  | .exhausted => ⟨.exhausted,r.state,r.events⟩
  | .fault (.panic p) =>
    match profile with
    | .unwind => ⟨.returned (.ok (.error p)),r.state,r.events⟩
    | .abort => ⟨.fault (.abort p),r.state,r.events⟩
  | .fault e => ⟨.fault e,r.state,r.events⟩

/-- Run a destructor on normal return or unwinding. An abort, source div or
fuel exhaustion has no normal destructor step. Double panic becomes abort.
SpawnDenied is a panic-class runtime fault, not a source Result constructor. -/
def finalize {S A : Type} (profile : Profile) (action : Q S A) (drop : Q S Unit) : Q S A := fun w =>
  let r := action w
  let finish := fun (_ : Unit) =>
    let d := drop r.state
    let outcome := match d.outcome with
      | .returned (.ok _) => r.outcome
      | .returned (.fail e) => .returned (.fail e)
      | .returned .div => .returned .div
      | .exhausted => .exhausted
      | .fault (.panic p) =>
        match r.outcome with
        | .fault (.panic _) | .fault (.spawnDenied _) => .fault (.abort p)
        | _ => if profile == .abort then .fault (.abort p) else .fault (.panic p)
      | .fault e => .fault e
    ⟨outcome,d.state,r.events ++ d.events⟩
  match r.outcome with
  | .returned (.ok _) | .returned (.fail _) => finish ()
  | .fault (.panic p) => if profile == .abort then ⟨.fault (.abort p),r.state,r.events⟩ else finish ()
  | .fault (.spawnDenied _) => if profile == .abort then ⟨.fault (.abort []),r.state,r.events⟩ else finish ()
  | _ => r

def withActive {S A : Type} (runtime : Runtime S) (profile : Profile)
    (thread : Nat) (action : Q S A) : Q S A :=
  PV_V263_World.bind (runtime.answer (.tlsReplace thread true)) fun previous =>
    finalize profile action (runtime.answer (.tlsRestore thread previous))

def traverse {S A : Type} (f : Nat → Q S A) : List Nat → Q S (List A)
  | [] => lift (.ok [])
  | i::is => PV_V263_World.bind (f i) fun a =>
      PV_V263_World.bind (traverse f is) fun rest => lift (.ok (a::rest))

/-- All catches are collected before merge; the first SOURCE-order panic is
resumed. Inner Rust Result errors, when A is a Result, are ordinary values. -/
def merge {S A : Type} : List (Except Bytes (List A)) → Q S (List A)
  | [] => lift (.ok [])
  | .error p::_ => fun w => ⟨.fault (.panic p),w,[]⟩
  | .ok xs::rest => PV_V263_World.bind (merge rest) fun ys => lift (.ok (xs++ys))

theorem catch_return {S A : Type} (p : Profile) (a : A) (w : State S) :
    (catchPanic p (lift (.ok a)) w).outcome = .returned (.ok (.ok a)) := rfl

theorem catch_unwind {S A : Type} (payload : Bytes) (w : State S) :
    (catchPanic (A := A) .unwind (fun v => ⟨.fault (.panic payload),v,[]⟩) w).outcome =
      .returned (.ok (.error payload)) := rfl

theorem catch_abort {S A : Type} (payload : Bytes) (w : State S) :
    (catchPanic (A := A) .abort (fun v => ⟨.fault (.panic payload),v,[]⟩) w).outcome =
      .fault (.abort payload) := rfl

/-- This is an interpreter lemma, NOT a callback-termination assumption for P.
The callback law must be proved separately at the concrete reached closures. -/
theorem traverse_total {S A : Type} (f : Nat → Q S A)
    (law : ∀ i w, ∃ a, (f i w).outcome = .returned (.ok a))
    (indices : List Nat) (w : State S) :
    ∃ values, (traverse f indices w).outcome = .returned (.ok values) := by
  induction indices generalizing w with
  | nil => exact ⟨[],rfl⟩
  | cons i is ih =>
    obtain ⟨a,ha⟩ := law i w
    obtain ⟨rest,hr⟩ := ih (f i w).state
    exact ⟨a::rest,by simp only [traverse,PV_V263_World.bind,ha,hr,PV_V263_World.lift]⟩

theorem merge_first {S A : Type} (p q : Bytes) (rest : List (Except Bytes (List A))) (w : State S) :
    (merge (.error p::.error q::rest) w).outcome = .fault (.panic p) := rfl

#print axioms catchPanic
#print axioms finalize
#print axioms withActive
#print axioms traverse
#print axioms merge
#print axioms catch_return
#print axioms catch_unwind
#print axioms catch_abort
#print axioms traverse_total
#print axioms merge_first
end R1Z.PV_V263_WorkerControl
