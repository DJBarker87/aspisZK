import PV_L1D_ResultCoercion
set_option autoImplicit false
namespace PV_L1D_CallbackSafe
open Aeneas Aeneas.Std Result
open R1Z.SideChannelL1AttemptRecord
open PV_L1D_Logged

def callbacks (es : List Event) : List Nat :=
  es.filterMap fun | .call .callback n => some n | _ => none

theorem callbacks_append (xs ys : List Event) :
    callbacks (xs++ys) = callbacks xs ++ callbacks ys := List.filterMap_append
#print axioms callbacks_append

def Safe {A : Type} (x : Logged A) : Prop := callbacks x.events = []

theorem safe_bind {A B : Type} (x : Logged A) (f : A → Logged B)
    (hx : Safe x) (hf : ∀ a, Safe (f a)) : Safe (x >>= f) := by
  cases x with
  | mk events status =>
    cases status with
    | ok a =>
      change callbacks (events ++ (f a).events) = []
      rw [callbacks_append]
      change callbacks events = [] at hx
      rw [hx,hf a]
      rfl
    | fail e => exact hx
    | div => exact hx
#print axioms safe_bind

theorem safe_lift {A : Type} (r : Result A) : Safe (lift r) := rfl
#print axioms safe_lift
theorem safe_pure {A : Type} (a : A) : Safe (Pure.pure a : Logged A) := rfl
#print axioms safe_pure
theorem safe_observe {A : Type} (site : Call) (k : Nat) (r : Result A)
    (h : callbacks [.call site k] = []) : Safe (observe site k r) := h
#print axioms safe_observe
end PV_L1D_CallbackSafe
