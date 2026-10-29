import PV_B3P_EqualOkHead9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

/-- Rewrite a specified pure head; the later continuation stays opaque. -/
theorem lift_head_equal9 {α β : Type} (x : α) (f : α → Result β)
    (right : Result β) (h : f x=right) : (do let y ← lift x; f y)=right := h
#print axioms lift_head_equal9
end PV_B3P_Binding9227
