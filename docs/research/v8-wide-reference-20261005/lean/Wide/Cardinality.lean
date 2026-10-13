import Mathlib.Data.Fintype.Card
import Mathlib.AlgebraicTopology.SimplexCategory.Basic

set_option autoImplicit false

namespace AspisWide.Cardinality

/-- The cardinality of `Fin` is independent of the chosen enumeration.
The full import environment can select a SimplexCategory enumeration for
concrete dimensions; compare it symbolically with the standard instance. -/
/- The cached exact decoder interfaces retain this enumeration in concrete
`Fin` dimensions. Keep its defining module explicit here; the theorem below
abstracts the resulting cardinality through its supplied `Fintype` instance. -/
theorem card_fin_of_fintype (n : Nat) [finiteDomain : Fintype (Fin n)] :
    Fintype.card (Fin n) = n :=
  (@Fintype.card_congr (Fin n) (Fin n) finiteDomain (Fin.fintype n)
    (Equiv.refl (Fin n))).trans (Fintype.card_fin n)

/-- Remove a nonnegative branch budget before specializing the finite domain.
An arbitrary Fintype instance prevents enumeration during instance comparison. -/
theorem card_fin_lt_of_budget {domainSize curveDegree budget count : Nat}
    [Fintype (Fin domainSize)]
    (many : budget + (curveDegree * domainSize + 1) < count) :
    curveDegree * Fintype.card (Fin domainSize) < count := by
  rw [card_fin_of_fintype]
  exact (Nat.le_succ (curveDegree * domainSize)).trans_lt
    ((Nat.le_add_left _ _).trans_lt many)

#print axioms card_fin_of_fintype
#print axioms card_fin_lt_of_budget
end AspisWide.Cardinality
