import S9CombinedWideMulQM31HelperTotalExactV1
import S9PairMixedCallToSourceV1
import S9HighTermsTraceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairMixedNormalizedDecodeV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31

/-- Preserve the exact normalized coefficient and decode equation supplied by
the source mixed-operation totality theorem, while tying its output to the
same successful Pair call. -/
theorem pair_mixed_success_normalized_decode
    (x : PW) (q : PQ) (product : PW)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9PairMixedCallToSourceV1.pairToCurrentW x))
    (hmul : AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q = .ok product) :
    ∃ qnorm sourceProduct,
      AspisR1CurrentWide.field.wide_exact.canonical_qm31
        (AspisR1S9CombinedWideMulQM31HelperTotalExactV1.toCurrentQM
          (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ q)) = .ok qnorm ∧
      AspisR1CurrentWide.Proof.CanonicalQM qnorm ∧
      AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ q) = .ok sourceProduct ∧
      product = AspisR1S9PairMixedCallToSourceV1.srcToPairW sourceProduct ∧
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1S9GeneratedWideMulQM31V2.toWide
          (AspisR1S9PairCallerStepV1.toP6W product)) ∧
      AspisR1CurrentWide.Proof.decodeWide
        (AspisR1S9GeneratedWideMulQM31V2.toWide
          (AspisR1S9PairCallerStepV1.toP6W product)) =
        ⟨AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9CombinedWideMulQM31HelperTotalExactV1.toCurrentWide
              (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)).c0 *
            AspisR1CurrentWide.Proof.decodeQM qnorm,
         AspisR1CurrentWide.Proof.decodeQM
            (AspisR1S9CombinedWideMulQM31HelperTotalExactV1.toCurrentWide
              (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)).c1 *
            AspisR1CurrentWide.Proof.decodeQM qnorm⟩ := by
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
  obtain ⟨qnorm,sourceProductTotal,hqcall,hqcan,htotal,houtCan,hdecode⟩ :=
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
  refine ⟨qnorm,sourceProduct,hqcall,hqcan,hsource,hproduct,?_,?_⟩
  · rw [hcarrier]
    exact houtCan
  · rw [hcarrier]
    exact hdecode

#print axioms pair_mixed_success_normalized_decode

end AspisR1S9PairMixedNormalizedDecodeV1
