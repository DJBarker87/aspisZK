import S9PairMixedCanonicalDirectV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairMixedCanonicalP6V1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31

/-- Convenience form of the direct mixed canonicality theorem using the
standard public Pair-to-P6 canonicality predicate. -/
theorem pair_mixed_success_canonical_of_p6_left
    (x : PW) (q : PQ) (product : PW)
    (hx : AspisR1S9HighTermsTraceV1.canonicalW
      (AspisR1S9PairCallerStepV1.toP6W x))
    (hmul : AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q = .ok product) :
    AspisR1S9HighTermsTraceV1.canonicalW
      (AspisR1S9PairCallerStepV1.toP6W product) := by
  have hx' : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9PairMixedCallToSourceV1.pairToCurrentW x) := by
    change AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9GeneratedWideMulQM31V2.toWide
        (AspisR1S9PairCallerStepV1.toP6W x))
    exact hx
  exact AspisR1S9PairMixedCanonicalDirectV1.pair_mixed_success_canonical_of_left
    x q product hx' hmul

#print axioms pair_mixed_success_canonical_of_p6_left

end AspisR1S9PairMixedCanonicalP6V1
