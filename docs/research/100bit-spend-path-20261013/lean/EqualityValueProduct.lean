import EqualityValueAdapter
import R0P.SemDecision

set_option autoImplicit false

namespace AspisR1.EqualityValueAdapter

/-- Split the ten-factor model product exactly where the generated wrapper
initializes its accumulator with factor zero and starts the loop at index one. -/
theorem eqValue_split_initial (left right : Fin 10 → ExactQM) :
    R0P.SemSource.eqValue left right =
      factor (left 0) (right 0) *
        ∏ i : Fin 9, factor (left i.succ) (right i.succ) := by
  rw [R0P.SemSource.eqValue, Fin.prod_univ_succ]
  congr 1

#print axioms eqValue_split_initial

end AspisR1.EqualityValueAdapter
