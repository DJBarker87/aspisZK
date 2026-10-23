import S9PairTermCallCanonicalV1
import S9PairPrefixAllCallsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairFourTermCanonicalV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PU := Std.Usize

/-- The four canonical term values are the exact outputs of the four calls in
the successful Pair term prefix. Each witness retains its own reads and
operation successes; no separate call-success premise is introduced. -/
theorem pair_term_prefix_four_terms_canonical
    (ap1 : Array PW (4#usize)) (q41 q8 q12 : PQ)
    (perm3 : PU) (t0 t1 t2 t3 : PW)
    (hprefix : AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
      .ok (perm3,(t0,t1,t2,t3)))
    (hap1 : ∀ (j : PU) (v : AspisR1S9HelperP6.field.WideExact),
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v) :
    ∃ (w0 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
          (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 0#usize)
      (w1 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
          (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 1#usize)
      (w2 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
          (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 2#usize)
      (w3 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
          (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 3#usize),
      w0.term = t0 ∧ w1.term = t1 ∧ w2.term = t2 ∧ w3.term = t3 ∧
      w3.perm = perm3 ∧
      AspisR1S9HighTermsTraceV1.canonicalW
        (AspisR1S9PairCallerStepV1.toP6W t0) ∧
      AspisR1S9HighTermsTraceV1.canonicalW
        (AspisR1S9PairCallerStepV1.toP6W t1) ∧
      AspisR1S9HighTermsTraceV1.canonicalW
        (AspisR1S9PairCallerStepV1.toP6W t2) ∧
      AspisR1S9HighTermsTraceV1.canonicalW
        (AspisR1S9PairCallerStepV1.toP6W t3) := by
  obtain ⟨w0,w1,w2,w3,ht0,ht1,ht2,ht3,hperm3⟩ :=
    AspisR1S9PairPrefixAllCallsV1.pair_term_prefix_four_same_run_calls
      ap1 q41 q8 q12 perm3 t0 t1 t2 t3 hprefix
  have hc0 := AspisR1S9PairTermCallCanonicalV1.pair_term_call_canonical
    ap1 (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 0#usize w0 hap1
  have hc1 := AspisR1S9PairTermCallCanonicalV1.pair_term_call_canonical
    ap1 (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 1#usize w1 hap1
  have hc2 := AspisR1S9PairTermCallCanonicalV1.pair_term_call_canonical
    ap1 (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 2#usize w2 hap1
  have hc3 := AspisR1S9PairTermCallCanonicalV1.pair_term_call_canonical
    ap1 (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 3#usize w3 hap1
  rw [ht0] at hc0
  rw [ht1] at hc1
  rw [ht2] at hc2
  rw [ht3] at hc3
  exact ⟨w0,w1,w2,w3,ht0,ht1,ht2,ht3,hperm3,hc0,hc1,hc2,hc3⟩

#print axioms pair_term_prefix_four_terms_canonical

end AspisR1S9PairFourTermCanonicalV1
