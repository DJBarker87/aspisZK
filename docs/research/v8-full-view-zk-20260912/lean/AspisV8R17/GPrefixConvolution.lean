import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Order

/-! The 271-term numerator and 479-term inverse prefix cannot wrap in a
1024-point cyclic convolution. This is only the no-alias algebra; correctness
of the FFT implementation, generated spectrum and source field remains a
separate refinement obligation. No privacy or hiding premise is introduced. -/
set_option autoImplicit false
namespace AspisV8R17

theorem fin271_fin479_add_mod1024 (i : Fin 271) (k : Fin 479) :
    (i.val + k.val) % 1024 = i.val + k.val := by
  have hi : i.val < 271 := i.isLt
  have hk : k.val < 479 := k.isLt
  omega

theorem gprefix_convolution_mod_eq_plain
    {F : Type*} [CommSemiring F]
    (a : Fin 271 → F) (b : Fin 479 → F) (j : Nat) :
    (∑ i : Fin 271, ∑ k : Fin 479,
      if (i.val + k.val) % 1024 = j then a i * b k else 0) =
    (∑ i : Fin 271, ∑ k : Fin 479,
      if i.val + k.val = j then a i * b k else 0) := by
  simp only [fin271_fin479_add_mod1024]

theorem gprefix_truncate_inverse
    {F : Type*} [CommSemiring F] (a : Fin 271 → F) (b c : Nat → F)
    (h : ∀ n, n < 479 → b n = c n) (j : Nat) (hj : j < 479) :
    (∑ i : Fin 271, if i.val ≤ j then a i * b (j-i.val) else 0) =
    (∑ i : Fin 271, if i.val ≤ j then a i * c (j-i.val) else 0) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [h (j-i.val) (by omega)]

#print axioms fin271_fin479_add_mod1024
#print axioms gprefix_convolution_mod_eq_plain
#print axioms gprefix_truncate_inverse
end AspisV8R17
