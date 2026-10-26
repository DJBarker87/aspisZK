import Aeneas
set_option autoImplicit false
namespace R1Z.PDict_RowBounds244
open Aeneas Aeneas.Std

theorem append_bound (left right : List U16)
    (hl : ∀ x ∈ left, x.val < 1024) (hr : ∀ x ∈ right, x.val < 1024) :
    ∀ x ∈ left++right, x.val < 1024 := by
  intro x member
  exact (List.mem_append.mp member).elim (hl x) (hr x)

#print axioms append_bound
end R1Z.PDict_RowBounds244
