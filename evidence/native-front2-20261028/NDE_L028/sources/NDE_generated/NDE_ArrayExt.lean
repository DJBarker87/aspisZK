import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_ArrayExt

theorem words {α : Type} {n : Usize} (a b : Array α n)
    (h : ∀ i : Nat, a.val[i]? = b.val[i]?) : a = b := by
  apply Subtype.ext
  exact List.ext_getElem? h

#print axioms words
end NDE_ArrayExt
