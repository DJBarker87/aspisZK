import PV_L1_FixedEvents
set_option autoImplicit false
namespace PV_L1_FixedBind
open Aeneas Aeneas.Std
open R1Z.SideChannelL1AttemptRecord (Event)
open PV_L1_Logged PV_L1_FixedEvents

theorem bind_fixed {A B : Type} (x : Logged A) (f : A → Logged B)
    (xs ys : List Event) (hx : Fixed xs x) (hf : ∀ a, Fixed ys (f a)) :
    Fixed (xs ++ ys) (x >>= f) := by
  rcases x with ⟨before,out⟩
  cases out with
  | ok a =>
    intro b result
    have same : (f a).result = .ok b := result
    change before ++ (f a).events = xs ++ ys
    exact congrArg₂ List.append (hx a rfl) (hf a b same)
  | fail e => intro b impossible; cases impossible
  | div => intro b impossible; cases impossible
#print axioms bind_fixed
end PV_L1_FixedBind
