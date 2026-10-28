import PV_B3P_Install133
namespace PV_B3P_Extensionality133
open Aeneas Aeneas.Std
set_option autoImplicit false

-- A universally quantified valid index is equivalent to whole-vector equality.
-- The index is auxiliary; it places no restriction on the function input.
theorem vec_ext {α : Type} (a b : alloc.vec.Vec α)
    (hlen : a.val.length = b.val.length)
    (hget : ∀ (i : Nat) (ha : i < a.val.length) (hb : i < b.val.length),
      a.val[i] = b.val[i]) : a = b := by
  apply Subtype.ext
  exact List.ext_getElem hlen hget

#print axioms vec_ext
end PV_B3P_Extensionality133
