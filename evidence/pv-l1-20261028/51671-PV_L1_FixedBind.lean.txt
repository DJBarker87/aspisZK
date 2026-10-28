import PV_L1_FixedEvents
set_option autoImplicit false
namespace PV_L1_FixedBind
open Aeneas Aeneas.Std
open R1Z.SideChannelL1AttemptRecord (Event)
open PV_L1_Logged PV_L1_FixedEvents

theorem bind_fixed {A B : Type} (x : Logged A) (f : A → Logged B)
    (xs ys : List Event) (hx : Fixed xs x) (hf : ∀ a, Fixed ys (f a)) :
    Fixed (xs ++ ys) (x >>= f) := by
  cases h : x.result with
  | ok a =>
    intro b result
    have same : (f a).result = .ok b := by
      simpa only [PV_L1_Logged.bind,h] using result
    change (match x.result with
      | .ok v => let y := f v; {events := x.events ++ y.events,result := y.result}
      | .fail e => {events := x.events,result := .fail e}
      | .div => {events := x.events,result := .div}).events = _
    rw [h]
    exact congrArg₂ List.append (hx a h) (hf a b same)
  | fail e => intro b impossible; simp only [PV_L1_Logged.bind,h] at impossible; cases impossible
  | div => intro b impossible; simp only [PV_L1_Logged.bind,h] at impossible; cases impossible
#print axioms bind_fixed
end PV_L1_FixedBind
