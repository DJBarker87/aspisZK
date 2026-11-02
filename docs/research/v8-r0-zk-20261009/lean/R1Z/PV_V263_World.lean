import PV_RJ4IDB_NativeTrace
import R1Z.PV_RunJoin_NativeFrames63
/-! V263 runtime substrate, NOT a source binding or an installed operation.
S carries the complete base/heap/OS world (EVH Runtime.State is a possible S).
Faults retain post-state/events and have no source Result projection. -/
set_option autoImplicit false
namespace R1Z.PV_V263_World
open Aeneas Aeneas.Std
open PV_RJ4IDB (Bytes NativeEvent)

structure State (S : Type) where
  base : S
  activeTLS : List (Nat × Bool) := []
  liveHandles : List Nat := []
  nextHandle : Nat := 0

inductive Fault where
  | spawnDenied (code : Int)
  | allocationDenied (size align : Nat)
  | panic (payload : Bytes)
  | abort (payload : Bytes)

inductive Outcome (A : Type) where
  | returned (result : Result A)
  | fault (error : Fault)
  | exhausted

structure Run (S A : Type) where
  outcome : Outcome A
  state : State S
  events : List NativeEvent

abbrev Q (S A : Type) := State S → Run S A

def lift {S A : Type} (r : Result A) : Q S A := fun w => ⟨.returned r,w,[]⟩

def bind {S A B : Type} (m : Q S A) (k : A → Q S B) : Q S B := fun w =>
  let r := m w
  match r.outcome with
  | .fault e => ⟨.fault e,r.state,r.events⟩
  | .exhausted => ⟨.exhausted,r.state,r.events⟩
  | .returned (.fail e) => ⟨.returned (.fail e),r.state,r.events⟩
  | .returned .div => ⟨.returned .div,r.state,r.events⟩
  | .returned (.ok a) =>
    let s := k a r.state
    ⟨s.outcome,s.state,r.events ++ s.events⟩

def sourceProjection {A : Type} : Outcome A → Option (Result A)
  | .returned r => some r
  | .fault _ => none
  | .exhausted => none

theorem bind_assoc {S A B C : Type} (m : Q S A) (k : A → Q S B) (f : B → Q S C) :
    bind (bind m k) f = bind m (fun a => bind (k a) f) := by
  funext w
  cases hm : (m w).outcome with
  | fault e => simp only [bind,hm]
  | exhausted => simp only [bind,hm]
  | returned r =>
    cases r with
    | fail e => simp only [bind,hm]
    | div => simp only [bind,hm]
    | ok a =>
      cases hk : (k a (m w).state).outcome with
      | fault e => simp only [bind,hm,hk,List.append_assoc]
      | exhausted => simp only [bind,hm,hk,List.append_assoc]
      | returned s => cases s <;> simp only [bind,hm,hk,List.append_assoc]

theorem fault_no_source {A : Type} (e : Fault) :
    sourceProjection (Outcome.fault (A := A) e) = none := rfl

theorem divergence_has_source {A : Type} :
    sourceProjection (Outcome.returned (A := A) .div) = some .div := rfl

theorem exhaustion_not_divergence {A : Type} :
    Outcome.exhausted (A := A) ≠ .returned .div := by intro h; cases h

#print axioms State
#print axioms Fault
#print axioms Outcome
#print axioms Run
#print axioms Q
#print axioms lift
#print axioms bind
#print axioms sourceProjection
#print axioms bind_assoc
#print axioms fault_no_source
#print axioms divergence_has_source
#print axioms exhaustion_not_divergence
end R1Z.PV_V263_World
