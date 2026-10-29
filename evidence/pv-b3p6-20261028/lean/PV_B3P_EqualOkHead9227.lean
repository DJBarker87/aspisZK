import PV_B3P_DigestBranchEq9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std
set_option autoImplicit false

/-- Eliminate just the leading Ok join, keeping the continuation opaque. -/
theorem equal_ok_head9 {α β : Type} (x : α) (f : α → Result β)
    (right : Result β) (h : f x=right) : (Result.ok x >>= f)=right := h
#print axioms equal_ok_head9
end PV_B3P_Binding9227
