import S9PairMixedCallToSourceV1
import S9CombinedWideMulQM31HelperTotalExactV1
import S9HighTermsTraceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairMixedCanonicalDirectV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31

/-- A same-call Pair mixed product is canonical whenever its left operand is
canonical in the public P6 embedding. The right operand is unrestricted: the
actual mixed operation normalizes it internally. -/
theorem pair_mixed_success_canonical_of_left
    (x : PW) (q : PQ) (product : PW)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9PairMixedCallToSourceV1.pairToCurrentW x))
    (hmul : AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q = .ok product) :
    AspisR1S9HighTermsTraceV1.canonicalW
      (AspisR1S9PairCallerStepV1.toP6W product) := by
  obtain ⟨sourceProduct,hsource,hproduct⟩ :=
    AspisR1S9PairMixedCallToSourceV1.pair_mul_qm31_success_reflects_source
      x q product hx hmul
  have hinput :
      AspisR1S9CombinedWideMulQM31HelperTotalExactV1.toCurrentWide
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x) =
      AspisR1S9PairMixedCallToSourceV1.pairToCurrentW x := by
    cases x <;> rfl
  have hxsource : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CombinedWideMulQM31HelperTotalExactV1.toCurrentWide
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)) := by
    rw [hinput]
    exact hx
  obtain ⟨qnorm,sourceProductTotal,hqcall,hqcan,htotal,houtCan,_hdecode⟩ :=
    AspisR1S9CombinedWideMulQM31HelperTotalExactV1.combined_wide_mul_qm31_total_exact
      (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)
      (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ q) hxsource
  have hsame : sourceProduct = sourceProductTotal :=
    Result.ok.inj (hsource.symm.trans htotal)
  have hcarrier :
      AspisR1S9GeneratedWideMulQM31V2.toWide
        (AspisR1S9PairCallerStepV1.toP6W product) =
      AspisR1S9CombinedWideMulQM31HelperTotalExactV1.toCurrentWide sourceProductTotal := by
    rw [hproduct, hsame]
    cases sourceProductTotal <;> rfl
  change AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1S9GeneratedWideMulQM31V2.toWide
      (AspisR1S9PairCallerStepV1.toP6W product))
  rw [hcarrier]
  exact houtCan

#print axioms pair_mixed_success_canonical_of_left

end AspisR1S9PairMixedCanonicalDirectV1
