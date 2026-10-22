import S9CandidateBodyEvidenceV1
import S9CandidateBodyArrayBridgeV1
import S9CandidateHighArraySemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateTermArrayToP6V1

open AspisR1S9CandidateBodyPrefixV1
open AspisR1S9CandidateBodyEvidenceV1
open AspisR1S9CandidateBodyTermsV1
open AspisR1S9CandidateBodyArrayBridgeV1
open AspisR1S9CandidateHighArraySemanticsV1
open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev U := Std.Usize
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev CArray := Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize)

/-- The exact candidate body success supplies its own q-power and term-call
results. Given only canonical source inputs, its four explicit term outputs
map to the four ordered callbacks and returned array of the retained P6 model.
No child-call success or intermediate value is an independent premise. -/
theorem candidate_body_terms_map_to_p6
    (ap0 ap1 : CArray) (extra : Array CQ (2#usize))
    (iter iterNext : core.ops.range.Range U) (side : U) (weights : CArray)
    (flow : ControlFlow (core.ops.range.Range U × CArray) CArray)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some side, iterNext))
    (hbody : _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra iter weights = .ok flow)
    (hextra : ∀ (j : U) (x : CQ), Array.index_usize extra j = .ok x →
      CanonicalP6 (AspisR1S9CandidateHelperV1.toP6Q x))
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x) :
    ∃ (q q1 q2 q3 unusedQ4 q4 q41 q8 q12 q16 : CQ)
      (low : AspisR1S9CandidateHelperV1.field.WideExact)
      (c0 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 0#usize)
      (c1 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 1#usize)
      (c2 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 2#usize)
      (c3 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 3#usize)
      (hterms : AspisR1S9HighTermsTraceV1.HighTermsFour
        (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
        (mapArray AspisR1S9CandidateHelperV1.toP6Q
          (candidateHigh q41 q8 q12))),
      Array.index_usize extra side = .ok q ∧
      AspisR1S9CandidateHelperV1.field.QM31.mul
        AspisR1S9CandidateHelperV1.field.QM31.ONE q = .ok q1 ∧
      AspisR1S9CandidateHelperV1.field.QM31.mul q1 q = .ok q2 ∧
      AspisR1S9CandidateHelperV1.field.QM31.mul q2 q = .ok q3 ∧
      AspisR1S9CandidateHelperV1.field.QM31.mul q3 q = .ok unusedQ4 ∧
      Array.index_usize
        (Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3])
        2#usize = .ok q4 ∧
      AspisR1S9CandidateHelperV1.field.QM31.square q4 = .ok q41 ∧
      AspisR1S9CandidateHelperV1.field.QM31.square q41 = .ok q8 ∧
      AspisR1S9CandidateHelperV1.field.QM31.mul q8 q41 = .ok q12 ∧
      AspisR1S9CandidateHelperV1.field.QM31.square q8 = .ok q16 ∧
      _root_.AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor
        (Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3]) ap0 = .ok low ∧
      candidateAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low
        c3.perm c0.term c1.term c2.term c3.term = .ok flow ∧
      (mapArray AspisR1S9CandidateHelperV1.toP6W
        (candidateTerms c0.term c1.term c2.term c3.term)).val = hterms.terms.val := by
  obtain ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,c0,c1,c2,c3,
      hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,htail⟩ :=
    candidate_body_success_evidence ap0 ap1 extra iter iterNext side weights flow
      hnext hbody
  have hseed := hextra side q hq
  have hhigh := candidate_high_array_canonical q q1 q2 q3 q4 q41 q8 q12
    hseed hq1 hq2 hq3 hq4 hq41 hq8 hq12
  obtain ⟨hterms⟩ :=
    AspisR1S9HighTermsTraceV1.high_terms4_from_fn_p6
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q
        (candidateHigh q41 q8 q12)) hap1 hhigh
  have htermsArray := candidate_term_array_maps_to_high_terms
      ap1 (candidateHigh q41 q8 q12) c0 c1 c2 c3 hterms
  exact ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,c0,c1,c2,c3,hterms,
    hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,htail,htermsArray⟩

#print axioms candidate_body_terms_map_to_p6

end AspisR1S9CandidateTermArrayToP6V1
