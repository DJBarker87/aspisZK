import S9PairFourTermCanonicalV1
import S9PairCandidateAfterTermsMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairAfterLowFourTermCanonicalV1

abbrev PW := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev PU := Std.Usize
abbrev PR := core.ops.range.Range Std.Usize

/-- A successful `pairAfterLow` run supplies the exact four-term prefix and
its actual call witnesses. Under the public canonical-read contract for
`ap1`, those same four returned terms are canonical. The prefix and tail
successes are both projections of the single input run. -/
theorem pair_after_low_four_terms_canonical
    (ap1 : Array PW (4#usize)) (side : PU) (iterNext : PR)
    (weights : Array PW (4#usize)) (q41 q8 q12 q16 : PQ) (low : PW)
    (flow : ControlFlow (PR × Array PW (4#usize)) (Array PW (4#usize)))
    (hafter : AspisR1S9PairCallerBodyPrefixV1.pairAfterLow
      ap1 side iterNext weights q41 q8 q12 q16 low = .ok flow)
    (hap1 : ∀ (j : PU) (v : AspisR1S9HelperP6.field.WideExact),
      Array.index_usize
        (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
          AspisR1S9CandidateHelperV1.toP6W
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
            AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v) :
    ∃ (t0 t1 t2 t3 : PW) (perm3 : PU)
      (w0 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
        (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 0#usize)
      (w1 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
        (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 1#usize)
      (w2 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
        (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 2#usize)
      (w3 : AspisR1S9PairPrefixAllCallsV1.PairTermCallWitness ap1
        (AspisR1S9PairPrefixAllCallsV1.pairHigh q41 q8 q12) 3#usize),
      AspisR1S9PairTermPrefixMapV1.pairTermPrefix ap1 q41 q8 q12 =
        .ok (perm3,(t0,t1,t2,t3)) ∧
      Array.index_usize _root_.AspisR1S9PairCallerStepV1.weights.PERM
        3#usize = .ok perm3 ∧
      AspisR1S9PairCandidateAfterTermsMapV1.pairAfterTerms
        ap1 side iterNext weights q41 q8 q12 q16 low perm3 t0 t1 t2 t3 = .ok flow ∧
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
  obtain ⟨t0,t1,t2,t3,perm3,hprefix,hperm3,htail⟩ :=
    AspisR1S9PairCandidateAfterTermsMapV1.pair_after_low_terms_from_same_success
      ap1 side iterNext weights q41 q8 q12 q16 low flow hafter
  obtain ⟨w0,w1,w2,w3,ht0,ht1,ht2,ht3,hpermWitness,hc0,hc1,hc2,hc3⟩ :=
    AspisR1S9PairFourTermCanonicalV1.pair_term_prefix_four_terms_canonical
      ap1 q41 q8 q12 perm3 t0 t1 t2 t3 hprefix hap1
  exact ⟨t0,t1,t2,t3,perm3,w0,w1,w2,w3,
    hprefix,hperm3,htail,ht0,ht1,ht2,ht3,hpermWitness,hc0,hc1,hc2,hc3⟩

#print axioms pair_after_low_four_terms_canonical

end AspisR1S9PairAfterLowFourTermCanonicalV1
