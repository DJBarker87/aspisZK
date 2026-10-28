import PV_L1_Logged
set_option autoImplicit false
namespace PV_L1_FixedEvents
open Aeneas Aeneas.Std
open R1Z.SideChannelL1AttemptRecord (Event Call)
open PV_L1_Logged

def Fixed {α : Type} (events : List Event) (x : Logged α) : Prop :=
  ∀ a, x.result = .ok a → x.events = events

theorem fixed_lift {α : Type} (r : Result α) : Fixed [] (lift r) := by
  intro a h; rfl
#print axioms fixed_lift

theorem fixed_pure {α : Type} (a : α) : Fixed [] (Pure.pure a : Logged α) := by
  intro b h; rfl
#print axioms fixed_pure

theorem bind_lift {α β : Type} (r : Result α) (f : α → Logged β)
    (events : List Event) (h : ∀ a, Fixed events (f a)) :
    Fixed events (lift r >>= f) := by
  cases r with
  | ok a => simpa only [Fixed,bind,lift,List.nil_append] using h a
  | fail e => intro b impossible; cases impossible
  | div => intro b impossible; cases impossible
#print axioms bind_lift

theorem bind_observe {α β : Type} (r : Result α) (f : α → Logged β)
    (site : Call) (index : Nat) (events : List Event)
    (h : ∀ a, Fixed events (f a)) :
    Fixed (.call site index :: events) (observe site index r >>= f) := by
  cases r with
  | ok a =>
    intro b result
    have same : (f a).result = .ok b := result
    change [.call site index] ++ (f a).events = _
    rw [h a b same]
    rfl
  | fail e => intro b impossible; cases impossible
  | div => intro b impossible; cases impossible
#print axioms bind_observe
end PV_L1_FixedEvents
