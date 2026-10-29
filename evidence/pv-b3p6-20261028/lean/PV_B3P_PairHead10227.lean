import PV_B3P_LiftHeadEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std
set_option autoImplicit false

/-- Eliminate only the known borrow pair, without traversing its continuation. -/
theorem pair_head_equal10 {α β γ : Type} (a : α) (b : β)
    (f : α → β → Result γ) (right : Result γ) (h : f a b=right) :
    (match (a,b) with | (x,y) => f x y) = right := h
#print axioms pair_head_equal10
end PV_B3P_Binding10227
