import Mathlib.Algebra.BigOperators.Fin

/-! Concatenation needs only the literal additive monoid, not a projected
semiring instance. Arbitrary enumerations of the same carriers are allowed. -/
set_option autoImplicit false
namespace AspisV8.FiniteSumConcat
theorem concat {F : Type*} [AddCommMonoid F] (m n : ℕ)
    (whole : Fintype (Fin (m+n))) (left : Fintype (Fin m)) (right : Fintype (Fin n))
    (values : Fin (m+n) → F) :
    (∑ lane∈@Finset.univ (Fin (m+n)) whole, values lane)=
      (∑ lane∈@Finset.univ (Fin m) left, values (Fin.castAdd n lane))+
      (∑ lane∈@Finset.univ (Fin n) right, values (Fin.natAdd m lane)) := by
  have sameWhole : whole=Fin.fintype (m+n) := Subsingleton.elim _ _
  have sameLeft : left=Fin.fintype m := Subsingleton.elim _ _
  have sameRight : right=Fin.fintype n := Subsingleton.elim _ _
  cases sameWhole
  cases sameLeft
  cases sameRight
  exact Fin.sum_univ_add values
#print axioms concat
end AspisV8.FiniteSumConcat
