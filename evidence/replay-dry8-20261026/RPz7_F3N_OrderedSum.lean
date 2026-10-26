import RPz7_F3N_ClaimPolynomial
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3N_OrderedSum
open scoped BigOperators
attribute [local irreducible] HAdd.hAdd HMul.hMul HPow.hPow Finset.sum

theorem sum {A K : Type*} [AddCommMonoid K] (n : Nat) (xs : List A)
    (length : xs.length=n) (f : A → K) :
    (xs.map f).sum=∑ j : Fin n,f (xs[j.val]'(by omega)) := by
  subst n
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp

#print axioms sum
end AspisR1.F3N_OrderedSum
end
