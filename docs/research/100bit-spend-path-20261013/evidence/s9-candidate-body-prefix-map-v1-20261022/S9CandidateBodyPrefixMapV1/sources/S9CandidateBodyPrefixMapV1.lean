import S9CandidateTermArrayToP6V1
import S9CandidateScalarFactorFoldTransportV1
import S9CandidateExplicitPowersArrayBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateBodyPrefixMapV1

open AspisR1S9CandidateBodyPrefixV1
open AspisR1S9CandidateBodyTermsV1
open AspisR1S9CandidateBodyEvidenceV1
open AspisR1S9CandidateHighArraySemanticsV1
open AspisR1S9CandidateTermArrayToP6V1
open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev CArray := Array CW (4#usize)

/-- The actual candidate active-body call supplies its full scalar/power/term
prefix. The same candidate scalar_factor result maps to the retained P6 scalar
fold, while the four candidate term calls map to the retained P6 callback
trace. This keeps one successful body witness as the source of every value. -/
def CandidateBodyPrefixEvidence
    (ap0 ap1 : CArray) (extra : Array CQ (2#usize))
    (iter iterNext : R) (side : U) (weights : CArray)
    (flow : ControlFlow (R × CArray) CArray) : Prop :=
  ∃ (q q1 q2 q3 unusedQ4 q4 q41 q8 q12 q16 : CQ)
    (low : CW)
    (c0 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 0#usize)
    (c1 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 1#usize)
    (c2 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 2#usize)
    (c3 : CandidateTermCall ap1 (candidateHigh q41 q8 q12) 3#usize)
    (p6Values : Array AspisR1S9HelperP6.field.QM31 (4#usize))
    (hterms : AspisR1S9HighTermsTraceV1.HighTermsFour
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q
        (candidateHigh q41 q8 q12))),
      Array.index_usize extra side = .ok q ∧
      @AspisR1S9HelperP6.weights.kpowers AspisR1S9HelperP6PowerSemanticsV1.currentQMOps
        (4#usize) (AspisR1S9CandidateHelperV1.toP6Q q) = .ok p6Values ∧
      p6Values.val = [AspisR1S9CandidateHelperV1.toP6Q
        AspisR1S9CandidateHelperV1.field.QM31.ONE,
        AspisR1S9CandidateHelperV1.toP6Q q1, AspisR1S9CandidateHelperV1.toP6Q q2,
        AspisR1S9CandidateHelperV1.toP6Q q3] ∧
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
        (Array.make 4#usize [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3]) ap0
        = .ok low ∧
      candidateAfterTerms ap1 side iterNext weights q41 q8 q12 q16 low
        c3.perm c0.term c1.term c2.term c3.term = .ok flow ∧
      (mapArray AspisR1S9CandidateHelperV1.toP6W
        (candidateTerms c0.term c1.term c2.term c3.term)).val = hterms.terms.val ∧
      @AspisR1S9HelperP6.weights.Weights.scalar_factor
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps p6Values
        (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
        = .ok (AspisR1S9CandidateHelperV1.toP6W low)

/-- Lift exact generated candidate-body success into its actual mapped P6
prefix evidence. `hextra` and `hap1` describe the same source arrays; no
operation result or intermediate power is separately assumed. -/
theorem candidate_body_prefix_maps_to_p6
    (ap0 ap1 : CArray) (extra : Array CQ (2#usize))
    (iter iterNext : R) (side : U) (weights : CArray)
    (flow : ControlFlow (R × CArray) CArray)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter =
      .ok (some side, iterNext))
    (hbody : _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
      ap0 ap1 extra iter weights = .ok flow)
    (hextra : ∀ (j : U) (x : CQ), Array.index_usize extra j = .ok x →
      CanonicalP6 (AspisR1S9CandidateHelperV1.toP6Q x))
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x) :
    CandidateBodyPrefixEvidence ap0 ap1 extra iter iterNext side weights flow := by
  obtain ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,c0,c1,c2,c3,hterms,
      hq,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,hlow,htail,htermsArray⟩ :=
    candidate_body_terms_map_to_p6 ap0 ap1 extra iter iterNext side weights flow
      hnext hbody hextra hap1
  have hseed := hextra side q hq
  obtain ⟨p6Values,hkpowers,hpowerValues⟩ :=
    AspisR1S9CandidateExplicitPowersArrayBridgeV1.candidate_explicit_powers4_matches_p6
      q q1 q2 q3 unusedQ4 hseed hq1 hq2 hq3 hunused
  have hpowerArray : mapArray AspisR1S9CandidateHelperV1.toP6Q
      (Array.make 4#usize
        [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3]) = p6Values := by
    apply Subtype.ext
    change [AspisR1S9CandidateHelperV1.toP6Q
        AspisR1S9CandidateHelperV1.field.QM31.ONE,
      AspisR1S9CandidateHelperV1.toP6Q q1, AspisR1S9CandidateHelperV1.toP6Q q2,
      AspisR1S9CandidateHelperV1.toP6Q q3] = p6Values.val
    exact hpowerValues.symm
  have hlowMap := AspisR1S9CandidateScalarFactorFoldTransportV1.candidate_scalar_factor_maps_to_p6
    (Array.make 4#usize
      [AspisR1S9CandidateHelperV1.field.QM31.ONE,q1,q2,q3]) ap0
  rw [hlow] at hlowMap
  have hlowP6 :
      @AspisR1S9HelperP6.weights.Weights.scalar_factor
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps p6Values
        (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
        = .ok (AspisR1S9CandidateHelperV1.toP6W low) := by
    rw [← hpowerArray]
    simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hlowMap.symm
  exact ⟨q,q1,q2,q3,unusedQ4,q4,q41,q8,q12,q16,low,c0,c1,c2,c3,p6Values,hterms,
    hq,hkpowers,hpowerValues,hq1,hq2,hq3,hunused,hq4,hq41,hq8,hq12,hq16,
    hlow,htail,htermsArray,hlowP6⟩

#print axioms candidate_body_prefix_maps_to_p6

end AspisR1S9CandidateBodyPrefixMapV1
