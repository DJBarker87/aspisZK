import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_ArrayExt

theorem words {α : Type} {n : Usize} (a b : Array α n)
    (h : ∀ i : Nat, a.val[i]? = b.val[i]?) : a = b := by
  apply Subtype.ext
  exact List.ext_getElem? h

theorem bounded_words {α : Type} {n : Usize} (a b : Array α n)
    (h : ∀ i : Nat, i < n.val → a.val[i]? = b.val[i]?) : a = b := by
  apply words
  intro i
  by_cases hi : i < n.val
  · exact h i hi
  · rw [List.getElem?_eq_none (by have := a.property; omega),
        List.getElem?_eq_none (by have := b.property; omega)]

#print axioms words
#print axioms bounded_words
end NDE_ArrayExt
