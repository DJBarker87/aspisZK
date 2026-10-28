import R1Z.SideChannelL1AttemptRecord
set_option autoImplicit false
namespace PV_L1_Logged
open Aeneas Aeneas.Std
open R1Z.SideChannelL1AttemptRecord (Event Call)

/-- Keep the entered prefix on ordinary errors, extraction failure and the
partial-result marker. No success-only event reconstruction is used. -/
structure Logged (α : Type) where
  events : List Event
  result : Result α

def pure {α : Type} (a : α) : Logged α := ⟨[],.ok a⟩
def bind {α β : Type} (x : Logged α) (f : α → Logged β) : Logged β :=
  match x.result with
  | .ok a => let y := f a; ⟨x.events ++ y.events,y.result⟩
  | .fail e => ⟨x.events,.fail e⟩
  | .div => ⟨x.events,.div⟩
instance : Monad Logged where
  pure := pure
  bind := bind

def lift {α : Type} (r : Result α) : Logged α := ⟨[],r⟩
def observe {α : Type} (site : Call) (index : Nat) (r : Result α) : Logged α :=
  ⟨[.call site index],r⟩
def erase {α : Type} (x : Logged α) : Result α := x.result

theorem erase_pure {α : Type} (a : α) : erase (Pure.pure a : Logged α) = .ok a := rfl
#print axioms erase_pure
theorem erase_lift {α : Type} (r : Result α) : erase (lift r) = r := rfl
#print axioms erase_lift
theorem erase_observe {α : Type} (site : Call) (index : Nat) (r : Result α) :
    erase (observe site index r) = r := rfl
#print axioms erase_observe
theorem erase_bind {α β : Type} (x : Logged α) (f : α → Logged β) :
    erase (x >>= f) = (do let a ← erase x; erase (f a)) := by
  cases x with
  | mk events result => cases result <;> rfl
#print axioms erase_bind
end PV_L1_Logged
