import S9PairMixedInputCanonicalV1
import S9CombinedWideMulQM31HelperTotalExactV1
import S9HighTermsTraceV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairMixedProductCanonicalV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev U := Std.Usize

/-- A successful Pair mixed call has a canonical mapped product when its
same-run left array read is canonical. The source-cut totality theorem supplies
canonicality of the identical returned output; no success is assumed. -/
theorem pair_mixed_success_product_canonical
    (ap1 : Array PW (4#usize)) (i : U) (x : PW) (q : PQ) (product : PW)
    (hread : Array.index_usize ap1 i = .ok x)
    (hap1 : ∀ (j : U) (v : AspisR1S9HelperP6.field.WideExact),
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v)
    (hmul : AspisR1S9PairCallerStepV1.field.WideExact.mul_qm31 x q = .ok product) :
    AspisR1S9HighTermsTraceV1.canonicalW
      (AspisR1S9PairCallerStepV1.toP6W product) := by
  obtain ⟨sourceProduct,hsource,hproduct⟩ :=
    AspisR1S9PairMixedInputCanonicalV1.pair_read_mixed_call_success_reflects_source
      ap1 i x q product hread hap1 hmul
  have hinput := AspisR1S9PairMixedInputCanonicalV1.pair_read_current_canonical
    ap1 i x hread hap1
  have hinputCarrier :
      AspisR1S9CombinedWideMulQM31HelperTotalExactV1.toCurrentWide
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x) =
      AspisR1S9PairMixedInputCanonicalV1.pairToCurrentW x := by
    cases x <;> rfl
  have hx : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9CombinedWideMulQM31HelperTotalExactV1.toCurrentWide
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)) := by
    rw [hinputCarrier]
    exact hinput
  obtain ⟨qnorm,sourceProductTotal,hqcall,hqcan,htotal,houtCan,_hdecode⟩ :=
    AspisR1S9CombinedWideMulQM31HelperTotalExactV1.combined_wide_mul_qm31_total_exact
      (AspisR1S9PairMixedCallToSourceV1.pairToSrcW x)
      (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ q) hx
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

#print axioms pair_mixed_success_product_canonical

end AspisR1S9PairMixedProductCanonicalV1
