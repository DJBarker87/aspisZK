import PV_EVH_Prefix
set_option autoImplicit false
namespace PV_EVH_Runtime
open Aeneas Aeneas.Std PV_EVH_World
open PV_RJ4IDB (Bytes NativeEvent)

structure Layout where
  size : Nat
  align : Nat
  deriving DecidableEq

structure Block where
  identity : Nat
  address : Nat
  layout : Layout
  bytes : Bytes
  owner : Nat

structure Handle where
  identity : Nat
  path : Bytes
  cursor : Nat
  live : Bool

/-- Runtime state is part of the world. No pure source value supplies the
allocator outcome, address, errno, heap, or handle identity. -/
structure State where
  base : World
  heap : List Block := []
  nextIdentity : Nat := 0
  handles : List Handle := []
  allocator : Bytes := []
  errno : Int := 0

inductive Fault where
  | allocationDenied (layout : Layout)
  | panic (message : Bytes)
  | abort (message : Bytes)
  | invalidMemory (identity : Nat)

inductive Outcome (A : Type) where
  | returned (result : Result A)
  | fault (error : Fault)
  | exhausted

structure Run (A : Type) where
  outcome : Outcome A
  state : State
  events : List NativeEvent

abbrev Q (A : Type) := State → Run A

def lift {A : Type} (r : Result A) : Q A := fun w => ⟨.returned r,w,[]⟩

def bind {A B : Type} (m : Q A) (k : A → Q B) : Q B := fun w =>
  let r := m w
  match r.outcome with
  | .fault e => ⟨.fault e,r.state,r.events⟩
  | .exhausted => ⟨.exhausted,r.state,r.events⟩
  | .returned (.fail e) => ⟨.returned (.fail e),r.state,r.events⟩
  | .returned .div => ⟨.returned .div,r.state,r.events⟩
  | .returned (.ok a) =>
    let s := k a r.state
    ⟨s.outcome,s.state,r.events ++ s.events⟩

instance : Monad Q where
  pure a := lift (.ok a)
  bind := bind

def sourceProjection {A : Type} : Outcome A → Option (Result A)
  | .returned r => some r
  | .fault _ => none
  | .exhausted => none

/-- Partial source view: runtime-fault runs have no source Result projection.
This law never establishes native adequacy, successful termination, or the
existence of a world in the source-view domain. -/
def PartialView {A : Type} (m : Q A) (source : Result A) : Prop :=
  ∀ w r, sourceProjection (m w).outcome = some r → source = r

theorem fault_no_source {A : Type} (error : Fault) :
    sourceProjection (Outcome.fault (A := A) error) = none := rfl

theorem fault_not_exhausted {A : Type} (error : Fault) :
    Outcome.fault (A := A) error ≠ .exhausted := by
  intro h
  cases h

theorem bind_fault {A B : Type} (m : Q A) (k : A → Q B)
    (w : State) (error : Fault) (h : (m w).outcome = .fault error) :
    bind m k w = ⟨.fault error,(m w).state,(m w).events⟩ := by
  simp only [bind,h]

theorem bind_exhausted {A B : Type} (m : Q A) (k : A → Q B)
    (w : State) (h : (m w).outcome = .exhausted) :
    bind m k w = ⟨.exhausted,(m w).state,(m w).events⟩ := by
  simp only [bind,h]

theorem bind_ok {A B : Type} (m : Q A) (k : A → Q B)
    (w : State) (a : A) (h : (m w).outcome = .returned (.ok a)) :
    bind m k w = ⟨(k a (m w).state).outcome,(k a (m w).state).state,
      (m w).events ++ (k a (m w).state).events⟩ := by
  simp only [bind,h]

theorem bind_assoc {A B C : Type} (m : Q A) (k : A → Q B) (f : B → Q C) :
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

theorem lift_view {A : Type} (r : Result A) : PartialView (lift r) r := by
  intro w s hs
  exact Option.some.inj hs

theorem bind_view {A B : Type} (m : Q A) (k : A → Q B)
    (r : Result A) (f : A → Result B) (hm : PartialView m r)
    (hk : ∀ a, PartialView (k a) (f a)) :
    PartialView (bind m k) (Aeneas.Std.bind r f) := by
  intro w s hs
  cases he : (m w).outcome with
  | fault e => simp only [bind,he,sourceProjection] at hs; cases hs
  | exhausted => simp only [bind,he,sourceProjection] at hs; cases hs
  | returned t =>
    have hr : r = t := hm w t (by rw [he]; rfl)
    rw [hr]
    cases t with
    | fail e => simp only [bind,he,sourceProjection] at hs; cases hs; rfl
    | div => simp only [bind,he,sourceProjection] at hs; cases hs; rfl
    | ok a =>
      simp only [bind,he] at hs
      exact hk a (m w).state s hs

#print axioms fault_no_source
#print axioms fault_not_exhausted
#print axioms bind_fault
#print axioms bind_exhausted
#print axioms bind_ok
#print axioms bind_assoc
#print axioms lift_view
#print axioms bind_view
end PV_EVH_Runtime
