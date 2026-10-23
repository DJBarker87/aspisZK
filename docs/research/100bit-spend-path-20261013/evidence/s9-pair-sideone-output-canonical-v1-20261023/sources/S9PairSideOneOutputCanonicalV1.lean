import S9PairSideOneCallV1
import S9PairFourTermCanonicalV1
import S9PairAddChainCanonicalV1
import S9PairMixedInputCanonicalV1
import S9PairQuarterTermCanonicalV1
import S9PairWideMulExactV1
import S9PairMixedCanonicalDirectV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairSideOneOutputCanonicalV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PU := Std.Usize
abbrev PR := AspisR1S9PairCallerBodyPrefixV1.R
abbrev PairArray := Array PW (4#usize)
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev P6W := AspisR1S9HelperP6.field.WideExact
abbrev P6MapW := AspisR1S9CandidateHelperV1.toP6W
abbrev PairP6W := AspisR1S9PairCallerStepV1.toP6W
abbrev PairMapW := AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

private theorem pair_current_carrier (x : PW) :
    AspisR1S9CurrentFieldOpsV1.toE (P6MapW (PairMapW x)) =
      AspisR1S9PairMixedInputCanonicalV1.pairToCurrentW x := by
  change AspisR1S9CurrentFieldOpsV1.toE
      (AspisR1S9CandidateHelperV1.toP6W
        (AspisR1S9PairCallerCandidateMapV1.pairToCandidateW x)) =
    AspisR1S9PairMixedInputCanonicalV1.pairToCurrentW x
  rw [AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW]
  rfl

private theorem pair_weights_read_canonical
    (weights : PairArray) (old1 : PW)
    (hread : Array.index_usize weights 1#usize = .ok old1)
    (hweights : ∀ (j : PU) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW weights)) j = .ok v →
      Canonical v) :
    Canonical (PairP6W old1) := by
  have hm1 := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result PairMapW weights 1#usize
  rw [hread] at hm1
  have hread1 : Array.index_usize (mapArray PairMapW weights) 1#usize = .ok (PairMapW old1) := by
    simpa only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hm1.symm
  have hm2 := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result
    P6MapW (mapArray PairMapW weights) 1#usize
  rw [hread1] at hm2
  have hread2 : Array.index_usize (mapArray P6MapW (mapArray PairMapW weights))
      1#usize = .ok (P6MapW (PairMapW old1)) := by
    simpa only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hm2.symm
  have hcan := hweights 1#usize (P6MapW (PairMapW old1)) hread2
  change Canonical (AspisR1S9PairCallerStepV1.toP6W old1)
  rw [← AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW old1]
  exact hcan

/-- The exact side-one suffix writes three canonical values. Canonicality
comes from the same call results exposed by the suffix inversion: bounded
wide products, unrestricted-right-operand mixed products, and the exact
ordered addition. The old slot-1 input is read from this execution. -/
theorem side_one_output_values_canonical
    (ap1 : PairArray) (iterNext : PR) (weights : PairArray)
    (q41 q8 q12 q16 : PQ) (low : PW) (perm3 : PU)
    (t0 t1 t2 t3 : PW)
    (flow : ControlFlow (PR × PairArray) PairArray)
    (htail : AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms
      ap1 1#usize iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 = .ok flow)
    (hterms : AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
      .ok (perm3,(t0,t1,t2,t3)))
    (hap1 : ∀ (j : PU) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v)
    (hweights : ∀ (j : PU) (v : P6W),
      Array.index_usize (mapArray P6MapW (mapArray PairMapW weights)) j = .ok v →
      Canonical v)
    (hlow : Canonical (PairP6W low)) :
    ∃ (output : PairArray) (sum1 allScaled first2Scaled : PW)
      (weights1 weights2 : PairArray),
      flow = .cont (iterNext, output) ∧
      Array.update weights 1#usize sum1 = .ok weights1 ∧
      Array.update weights1 2#usize allScaled = .ok weights2 ∧
      Array.update weights2 3#usize first2Scaled = .ok output ∧
      Canonical (PairP6W sum1) ∧ Canonical (PairP6W allScaled) ∧
      Canonical (PairP6W first2Scaled) := by
  obtain ⟨output, first2, first3, all, old1, ap1perm, quarter, weighted, sum1,
      weights1, allProduct, allScaled, weights2, first2Product, first2Scaled, q10,
      h2, h3, hAll, hOld1, hRead, hQuarter, hWeighted, hSum1, hWeights1,
      hAllProduct, hAllScaled, hWeights2, hFirst2Product, hQ10,
      hFirst2Scaled, hFlow, hOutput⟩ :=
    AspisR1S9PairSideOneCallV1.side_one_tail_exposes_calls
      ap1 iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 flow htail
  obtain ⟨_w0, _w1, _w2, _w3, _ht0, _ht1, _ht2, _ht3, _hperm3,
      ht0Can, ht1Can, ht2Can, ht3Can⟩ :=
    AspisR1S9PairFourTermCanonicalV1.pair_term_prefix_four_terms_canonical
      ap1 q41 q8 q12 perm3 t0 t1 t2 t3 hterms hap1
  obtain ⟨hfirst2Can, hfirst3Can, hallCan⟩ :=
    AspisR1S9PairAddChainCanonicalV1.pair_four_term_adds_canonical
      t0 t1 t2 t3 first2 first3 all ht0Can ht1Can ht2Can ht3Can h2 h3 hAll
  have hquarterInput := AspisR1S9PairMixedInputCanonicalV1.pair_read_current_canonical
    ap1 perm3 ap1perm hRead hap1
  have hquarterCan := AspisR1S9PairQuarterTermCanonicalV1.pair_quarter_term_success_canonical
    ap1perm quarter hquarterInput hQuarter
  change Canonical (PairP6W quarter) at hquarterCan
  have hOld1Can := pair_weights_read_canonical weights old1 hOld1 hweights
  obtain ⟨_wide1, _source1, _mapped1, hWeightedCan, _decode1⟩ :=
    AspisR1S9PairWideMulExactV1.pair_mul_success_exact low quarter weighted
      hlow hquarterCan hWeighted
  have hSum1Can := AspisR1S9PairAddChainCanonicalV1.pair_add_success_canonical
    old1 weighted sum1 hOld1Can hWeightedCan hSum1
  change Canonical (PairP6W sum1) at hSum1Can
  obtain ⟨_wide2, _source2, _mapped2, hAllProductCan, _decode2⟩ :=
    AspisR1S9PairWideMulExactV1.pair_mul_success_exact low all allProduct
      hlow hallCan hAllProduct
  have hAllProductCurrent : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9PairMixedInputCanonicalV1.pairToCurrentW allProduct) := by
    rw [← pair_current_carrier allProduct]
    exact hAllProductCan
  have hAllScaledCan := AspisR1S9PairMixedCanonicalDirectV1.pair_mixed_success_canonical_of_left
    allProduct q41 allScaled hAllProductCurrent hAllScaled
  change Canonical (PairP6W allScaled) at hAllScaledCan
  obtain ⟨_wide3, _source3, _mapped3, hFirst2ProductCan, _decode3⟩ :=
    AspisR1S9PairWideMulExactV1.pair_mul_success_exact low first2 first2Product
      hlow hfirst2Can hFirst2Product
  have hFirst2ProductCurrent : AspisR1CurrentWide.Proof.CanonicalWide
      (AspisR1S9PairMixedInputCanonicalV1.pairToCurrentW first2Product) := by
    rw [← pair_current_carrier first2Product]
    exact hFirst2ProductCan
  have hFirst2ScaledCan := AspisR1S9PairMixedCanonicalDirectV1.pair_mixed_success_canonical_of_left
    first2Product q10 first2Scaled
    hFirst2ProductCurrent hFirst2Scaled
  change Canonical (PairP6W first2Scaled) at hFirst2ScaledCan
  exact ⟨output, sum1, allScaled, first2Scaled, weights1, weights2,
    hFlow, hWeights1, hWeights2, hOutput, hSum1Can, hAllScaledCan, hFirst2ScaledCan⟩

#print axioms side_one_output_values_canonical

end AspisR1S9PairSideOneOutputCanonicalV1
