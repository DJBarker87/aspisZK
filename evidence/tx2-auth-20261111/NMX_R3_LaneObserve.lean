import NMX_R3_LaneCarrier
import NMX_R3_LaneCuts
set_option autoImplicit false
namespace NMX_R3_LaneObserve
open Aeneas Aeneas.Std Result
abbrev Native := core.result.Result NCV_Reference.Lane Unit

def observe (r : Result Native) : Result (Option RSL.LaneState) :=
 r >>= fun a => ok (NMX_R3_LaneCarrier.result a)

theorem returned (r : Native) : observe (ok r) = ok (NMX_R3_LaneCarrier.result r) := rfl

theorem through_if (p : Prop) [Decidable p] (a b : Result Native) :
 observe (if p then a else b) = if p then observe a else observe b := by
 by_cases h : p <;> simp only [h, ↓reduceIte]

theorem pure_if {α : Type} (p : Prop) [Decidable p] (a b : α) :
 (if p then (ok a : Result α) else ok b) = ok (if p then a else b) := by
 by_cases h : p <;> simp only [h, ↓reduceIte]

theorem failed (e : Error) : observe (fail e) = fail e := rfl

theorem diverged : observe div = div := rfl
#print axioms returned
#print axioms through_if
#print axioms pure_if
#print axioms failed
#print axioms diverged
end NMX_R3_LaneObserve
