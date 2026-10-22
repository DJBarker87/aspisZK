import S9CandidateBodyTermsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateBodyEvidenceV1

open AspisR1S9CandidateBodyPrefixV1
open AspisR1S9CandidateBodyTermsV1
open AspisR1S9CandidateHelperV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev W := Array field.WideExact (4#usize)
abbrev Q := field.QM31

/-- A successful active candidate-body call, decomposed into the exact
same-call prefix, four explicit term-call records, and the remaining exact
continuation. This is proposition-valued evidence: all returned values are
existential data and all equations are propositions. -/
theorem candidate_body_success_evidence
    (ap0 ap1 : W) (extra : Array Q (2#usize))
    (iter iterNext : R) (side : U) (weights : W)
    (flow : ControlFlow (R × W) W)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some side, iterNext))
    (hbody : _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra iter weights = .ok flow) :
    ∃ (q q1 q2 q3 unusedQ4 q4 q41 q8 q12 q16 : Q)
      (low : field.WideExact)
      (c0 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 0#usize)
      (c1 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 1#usize)
      (c2 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 2#usize)
      (c3 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 3#usize),
      Array.index_usize extra side = .ok q ∧
      field.QM31.mul field.QM31.ONE q = .ok q1 ∧
      field.QM31.mul q1 q = .ok q2 ∧
      field.QM31.mul q2 q = .ok q3 ∧
      field.QM31.mul q3 q = .ok unusedQ4 ∧
      Array.index_usize (Array.make 4#usize [field.QM31.ONE,q1,q2,q3]) 2#usize = .ok q4 ∧
      field.QM31.square q4 = .ok q41 ∧
      field.QM31.square q41 = .ok q8 ∧
      field.QM31.mul q8 q41 = .ok q12 ∧
      field.QM31.square q8 = .ok q16 ∧
      _root_.AspisR1S9CandidateHelperV1.weights.Weights.scalar_factor
        (Array.make 4#usize [field.QM31.ONE,q1,q2,q3]) ap0 = .ok low ∧
      candidateAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low
        c3.perm c0.term c1.term c2.term c3.term = .ok flow := by
  have hactive := hbody
  rw [body_some_eq_candidateActiveBody ap0 ap1 extra iter iterNext side weights hnext] at hactive
  obtain ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,
      hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,hrest⟩ :=
    candidate_active_prefix_from_success ap0 ap1 extra side iterNext weights flow hactive
  obtain ⟨c0,c1,c2,c3,htail⟩ :=
    candidate_after_low_terms_from_success ap1 side iterNext weights q41 q8 q12 q16 low flow hrest
  exact ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,c0,c1,c2,c3,
    hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,htail⟩

#print axioms candidate_body_success_evidence

end AspisR1S9CandidateBodyEvidenceV1
