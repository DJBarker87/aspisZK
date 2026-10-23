import S9PairPrefixAllCallsV1
import S9PairMixedInputCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairFourMixedReflectionsV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PU := Std.Usize
abbrev SrcW := AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact

/-- All four mixed products in a successful actual Pair term prefix reflect
from their own same-run call results to the exact source-cut operation. The
only arithmetic-domain contract is canonicality of successful ap1 reads. -/
theorem pair_term_prefix_four_mixed_calls_reflect
    (ap1 : Array PW (4#usize)) (q41 q8 q12 : AspisR1S9PairCallerStepV1.field.QM31)
    (perm3 : PU) (t0 t1 t2 t3 : PW)
    (hprefix : AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
      .ok (perm3,(t0,t1,t2,t3)))
    (hap1 : ∀ (j : PU) (v : AspisR1S9HelperP6.field.WideExact),
      (Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)) j = .ok v) →
      AspisR1S9HighTermsTraceV1.canonicalW v) :
    ∃ (w0 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
        (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 0#usize)
      (w1 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
        (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 1#usize)
      (w2 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
        (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 2#usize)
      (w3 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
        (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 3#usize)
      (s0 s1 s2 s3 : SrcW),
      w0.term = t0 ∧ w1.term = t1 ∧ w2.term = t2 ∧ w3.term = t3 ∧
      w3.perm = perm3 ∧
      AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW w0.input)
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ w0.coefficient) = .ok s0 ∧
      w0.product = AspisR1S9PairMixedCallToSourceV1.srcToPairW s0 ∧
      AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW w1.input)
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ w1.coefficient) = .ok s1 ∧
      w1.product = AspisR1S9PairMixedCallToSourceV1.srcToPairW s1 ∧
      AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW w2.input)
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ w2.coefficient) = .ok s2 ∧
      w2.product = AspisR1S9PairMixedCallToSourceV1.srcToPairW s2 ∧
      AspisR1S9SquareMulQMCutV1.field.wide_exact.WideExact.mul_qm31
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcW w3.input)
        (AspisR1S9PairMixedCallToSourceV1.pairToSrcQ w3.coefficient) = .ok s3 ∧
      w3.product = AspisR1S9PairMixedCallToSourceV1.srcToPairW s3 := by
  obtain ⟨w0,w1,w2,w3,ht0,ht1,ht2,ht3,hperm3⟩ :=
    AspisR1S9PairPrefixAllCallsV1.pair_term_prefix_four_same_run_calls
      ap1 q41 q8 q12 perm3 t0 t1 t2 t3 hprefix
  obtain ⟨s0,hs0,heq0⟩ :=
    AspisR1S9PairMixedInputCanonicalV1.pair_read_mixed_call_success_reflects_source
      ap1 w0.perm w0.input w0.coefficient w0.product w0.inputRead hap1 w0.mixedSuccess
  obtain ⟨s1,hs1,heq1⟩ :=
    AspisR1S9PairMixedInputCanonicalV1.pair_read_mixed_call_success_reflects_source
      ap1 w1.perm w1.input w1.coefficient w1.product w1.inputRead hap1 w1.mixedSuccess
  obtain ⟨s2,hs2,heq2⟩ :=
    AspisR1S9PairMixedInputCanonicalV1.pair_read_mixed_call_success_reflects_source
      ap1 w2.perm w2.input w2.coefficient w2.product w2.inputRead hap1 w2.mixedSuccess
  obtain ⟨s3,hs3,heq3⟩ :=
    AspisR1S9PairMixedInputCanonicalV1.pair_read_mixed_call_success_reflects_source
      ap1 w3.perm w3.input w3.coefficient w3.product w3.inputRead hap1 w3.mixedSuccess
  exact ⟨w0,w1,w2,w3,s0,s1,s2,s3,ht0,ht1,ht2,ht3,hperm3,hs0,heq0,hs1,heq1,hs2,heq2,hs3,heq3⟩

#print axioms pair_term_prefix_four_mixed_calls_reflect

end AspisR1S9PairFourMixedReflectionsV1
