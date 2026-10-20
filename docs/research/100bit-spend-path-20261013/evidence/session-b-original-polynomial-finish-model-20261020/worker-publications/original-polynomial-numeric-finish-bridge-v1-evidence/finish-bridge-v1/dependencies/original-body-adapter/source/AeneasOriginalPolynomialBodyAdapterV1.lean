import AeneasCurrentWidePolynomialFoldConsumerV1

set_option autoImplicit false

namespace AspisR1CurrentWide.OriginalPolynomialBodyAdapter

open Aeneas Aeneas.Std Result
open AspisR1CurrentWide.Proof

/-- Operational port of the whole original emitted polynomial body after
    replacing the generated `Rev.fold` callee by the pinned Aeneas `Rev.next`
    loop, and mapping the generated accumulator/captured `(x, bytes)` closure
    through the checked current-Wide callback.  The body checker pins the
    complete original declaration and all of these substitutions. -/
def originalEmittedPolynomialBody (bytes : Slice U8) (x : E) : Result E :=
  AspisR1CurrentWide.RevFoldRefinementV2.actualRfoldLoop 8
    AspisR1CurrentWide.RevFoldRefinementV2.actualInitialRevRange
    (AspisR1CurrentWide.AeneasPolynomialConsumer.currentPolynomialStep bytes x)
    currentWideZero

/-- The operationally ported original body agrees with the seven ordered
    coefficient updates for every result, including parser and arithmetic
    failures. -/
theorem originalEmittedPolynomialBody_eq_unrolled
    (bytes : Slice U8) (x : E) :
    originalEmittedPolynomialBody bytes x = current_unrolled_record_polynomial bytes x := by
  exact AspisR1CurrentWide.AeneasPolynomialConsumer.actual_loop_eq_current_unrolled bytes x

theorem originalEmittedPolynomialBody_success_iff_unrolled
    (bytes : Slice U8) (x out : E) :
    originalEmittedPolynomialBody bytes x = .ok out ↔
      current_unrolled_record_polynomial bytes x = .ok out := by
  rw [originalEmittedPolynomialBody_eq_unrolled]

#print axioms originalEmittedPolynomialBody_eq_unrolled
#print axioms originalEmittedPolynomialBody_success_iff_unrolled

end AspisR1CurrentWide.OriginalPolynomialBodyAdapter
