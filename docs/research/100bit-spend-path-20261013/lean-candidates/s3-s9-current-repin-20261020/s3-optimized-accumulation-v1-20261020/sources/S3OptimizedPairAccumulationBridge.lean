import S3OptimizedInactiveTableBridge

set_option autoImplicit false
namespace AspisR1.S3OptimizedPairAccumulationBridge

open AspisR1.S3S9CurrentSourceModel

/-- The coefficient array after the Rust `for j in 0..64` accumulation.
The `field(f,j)` parser is deliberately represented by `coeff`; its byte
decoding is a separate source boundary. -/
def coefficientsAfterLoop {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (g : Fin 12) : E :=
  ∑ j : Fin 64, if groupAt j = g then coeff j else 0

/-- The `weight` local after the Rust inner bit loop for one mask group. -/
def weightAfterLoop {E : Type} [CommSemiring E]
    (low : Fin 16 → E) (g : Fin 12) : E :=
  ∑ s : Fin 16, if inactiveAtGroup g s then low s else 0

/-- The final accumulation performed by the Rust outer group loop, with the
two preceding loop results made explicit. -/
def optimizedPairAfterLoops {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E) : E :=
  ∑ g : Fin 12,
    coefficientsAfterLoop coeff g * weightAfterLoop low g

theorem optimized_pair_accumulation_eq_groupedPair
    {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E) :
    optimizedPairAfterLoops coeff low = groupedPair coeff low groupAt inactiveAtGroup := by
  rfl

/-- The optimized S2 accumulation computes the exact same inactive-pair
functional as the current row classifier, for arbitrary decoded coefficients
and low challenges. This is the algebraic result of the three source loops;
the source snapshot checker pins their bounds, table lookups, and add/mul
updates. -/
theorem optimized_pair_accumulation_eq_rowFunctional
    {E : Type} [CommSemiring E]
    (coeff : Fin 64 → E) (low : Fin 16 → E) :
    optimizedPairAfterLoops coeff low =
      ungroupedPair coeff low inactiveAtSource := by
  rw [optimized_pair_accumulation_eq_groupedPair]
  exact s3_grouped_pair_exact coeff low

#print axioms optimized_pair_accumulation_eq_groupedPair
#print axioms optimized_pair_accumulation_eq_rowFunctional
end AspisR1.S3OptimizedPairAccumulationBridge
