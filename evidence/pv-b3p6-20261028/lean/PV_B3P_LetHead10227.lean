import PV_B3P_PairHead10227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std
set_option autoImplicit false

/-- Eliminate only a delayed pure restoration binding. -/
theorem let_head_equal10 {α β : Type} (value : α) (f : α → Result β)
    (right : Result β) (h : f value=right) : (let next := value; f next)=right := h
#print axioms let_head_equal10
end PV_B3P_Binding10227
