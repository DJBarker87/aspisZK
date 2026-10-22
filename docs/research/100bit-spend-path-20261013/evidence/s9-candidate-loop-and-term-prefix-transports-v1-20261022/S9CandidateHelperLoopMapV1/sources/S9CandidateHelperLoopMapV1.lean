import S9CandidateTwoBodyCallsV1
import S9CandidateBodyPrefixMapV1
import S9CandidateActiveBodyAssemblerV1
import S9FactoredLoopTwoStepV4
import S9FactoredLoopBodyShapeV3
import S3S9ConcreteFieldOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateHelperLoopMapV1

open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateFoldMapPrimitivesV1
open AspisR1S9CandidateBodyPrefixMapV1
open AspisR1S9CandidateActiveBodyAssemblerV1
open AspisR1S9CandidateBodyTermsV1
open AspisR1S9FactoredLoopTwoStepV4
open AspisR1S9CandidateTwoBodyCallsV1
open AspisR1S9FactoredLoopBodyShapeV3

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev CArray := Array CW (4#usize)
abbrev PArray := Array PW (4#usize)

def mapCandidateFlow (flow : ControlFlow (R × CArray) CArray) :
    ControlFlow (R × PArray) PArray :=
  match flow with
  | .done out => .done (mapArray AspisR1S9CandidateHelperV1.toP6W out)
  | .cont (iter, values) =>
      .cont (iter, mapArray AspisR1S9CandidateHelperV1.toP6W values)

/-- Given an actual successful generated-candidate helper call and the
canonical-read conditions used by the body prefix bridge, its retained P6
helper result uses the same two intermediate body calls and returned array.
The additional, still-unproved transport premise is the exact source-tail map
supplied by the side-specific candidate suffix proof; prefix arrays and
operation results come from the actual candidate body's two witnesses. This
is candidate-extraction correspondence, not a claim about frozen Std source.
-/
theorem candidate_helper_success_maps_to_p6_loop
    (ap0 ap1 : CArray) (extra : Array CQ (2#usize))
    (initial output : CArray)
    (hloop : _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop
      AspisR1S9CandidateTwoBodyCallsV1.start0 ap0 ap1 extra initial = .ok output)
    (hextra : ∀ (j : U) (x : CQ), Array.index_usize extra j = .ok x →
      AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
        (AspisR1S9CandidateHelperV1.toP6Q x))
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hsuffix : ∀ (side : U) (iterNext : R) (weights : CArray)
      (flow : ControlFlow (R × CArray) CArray)
      (q41 q8 q12 q16 : CQ) (low : CW) (perm3 : U)
      (t0 t1 t2 t3 : CW),
      Array.index_usize _root_.AspisR1S9CandidateHelperV1.weights.PERM 3#usize = .ok perm3 →
      AspisR1S9CandidateBodyTermsV1.candidateAfterTerms ap1 side iterNext weights
        q41 q8 q12 q16 low perm3 t0 t1 t2 t3 = .ok flow →
      @AspisR1S9CandidateActiveBodyAssemblerV1.p6AfterTerms
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
        (mapArray AspisR1S9CandidateHelperV1.toP6W
          (AspisR1S9CandidateBodyTermsV1.candidateTerms t0 t1 t2 t3))
        side iterNext (mapArray AspisR1S9CandidateHelperV1.toP6W weights)
        (AspisR1S9CandidateHelperV1.toP6W low)
        (AspisR1S9CandidateHelperV1.toP6Q q41)
        (AspisR1S9CandidateHelperV1.toP6Q q16) = .ok (mapCandidateFlow flow)) :
    @AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      AspisR1S9CandidateTwoBodyCallsV1.start0
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
      (mapArray AspisR1S9CandidateHelperV1.toP6W initial) =
      .ok (mapArray AspisR1S9CandidateHelperV1.toP6W output) := by
  letI : AspisR1S9HelperP6.FieldOps := AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
  obtain ⟨iter1,iter2,middle,hnext0,hstart1,hend1,hbody0,
    hnext1,hstart2,hend2,hbody1,hnext2,hbody2⟩ :=
    AspisR1S9CandidateTwoBodyCallsV1.helper_success_two_body_calls
      ap0 ap1 extra initial output hloop
  have hpref0 := AspisR1S9CandidateBodyPrefixMapV1.candidate_body_prefix_maps_to_p6
    ap0 ap1 extra AspisR1S9CandidateTwoBodyCallsV1.start0 iter1 0#usize initial
    (.cont (iter1,middle)) hnext0 hbody0 hextra hap1
  have hactive0 := AspisR1S9CandidateActiveBodyAssemblerV1.candidate_body_prefix_assembles_p6
    ap0 ap1 extra AspisR1S9CandidateTwoBodyCallsV1.start0 iter1 0#usize initial
    (.cont (iter1,middle)) (mapCandidateFlow (.cont (iter1,middle))) hpref0
    (by
      intro q41 q8 q12 q16 low perm3 t0 t1 t2 t3 hperm htail
      exact hsuffix 0#usize iter1 initial (.cont (iter1,middle))
        q41 q8 q12 q16 low perm3 t0 t1 t2 t3 hperm htail)
  have hbodyP60 : AspisR1S9FactoredLoopBodyShapeV3.body
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
      (AspisR1S9CandidateTwoBodyCallsV1.start0,
       mapArray AspisR1S9CandidateHelperV1.toP6W initial) =
      .ok (.cont (iter1,mapArray AspisR1S9CandidateHelperV1.toP6W middle)) := by
    rw [AspisR1S9FactoredLoopBodyShapeV3.body_some_eq_activeBody
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
      AspisR1S9CandidateTwoBodyCallsV1.start0 iter1 0#usize
      (mapArray AspisR1S9CandidateHelperV1.toP6W initial) hnext0]
    simpa only [mapCandidateFlow] using hactive0
  have hpref1 := AspisR1S9CandidateBodyPrefixMapV1.candidate_body_prefix_maps_to_p6
    ap0 ap1 extra iter1 iter2 iter1.start middle (.cont (iter2,output))
    hnext1 hbody1 hextra hap1
  have hactive1 := AspisR1S9CandidateActiveBodyAssemblerV1.candidate_body_prefix_assembles_p6
    ap0 ap1 extra iter1 iter2 iter1.start middle (.cont (iter2,output))
    (mapCandidateFlow (.cont (iter2,output))) hpref1
    (by
      intro q41 q8 q12 q16 low perm3 t0 t1 t2 t3 hperm htail
      exact hsuffix iter1.start iter2 middle (.cont (iter2,output))
        q41 q8 q12 q16 low perm3 t0 t1 t2 t3 hperm htail)
  have hbodyP61 : AspisR1S9FactoredLoopBodyShapeV3.body
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
      (iter1,mapArray AspisR1S9CandidateHelperV1.toP6W middle) =
      .ok (.cont (iter2,mapArray AspisR1S9CandidateHelperV1.toP6W output)) := by
    rw [AspisR1S9FactoredLoopBodyShapeV3.body_some_eq_activeBody
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
      iter1 iter2 iter1.start (mapArray AspisR1S9CandidateHelperV1.toP6W middle) hnext1]
    simpa only [mapCandidateFlow] using hactive1
  have hbodyP62 : AspisR1S9FactoredLoopBodyShapeV3.body
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
      (iter2,mapArray AspisR1S9CandidateHelperV1.toP6W output) =
      .ok (.done (mapArray AspisR1S9CandidateHelperV1.toP6W output)) := by
    unfold AspisR1S9FactoredLoopBodyShapeV3.body
      _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop.body
    rw [hnext2]
    rfl
  let p6step : R × PArray → Result (ControlFlow (R × PArray) PArray) :=
    AspisR1S9FactoredLoopBodyShapeV3.body
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
  have hp6loop : Aeneas.Std.loop p6step
      (AspisR1S9CandidateTwoBodyCallsV1.start0,
       mapArray AspisR1S9CandidateHelperV1.toP6W initial) =
      .ok (mapArray AspisR1S9CandidateHelperV1.toP6W output) := by
    dsimp only [p6step]
    rw [Aeneas.Std.loop.eq_def, hbodyP60]
    dsimp only
    rw [Aeneas.Std.loop.eq_def, hbodyP61]
    dsimp only
    rw [Aeneas.Std.loop.eq_def, hbodyP62]
  change @AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      AspisR1S9CandidateTwoBodyCallsV1.start0
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
      (mapArray AspisR1S9CandidateHelperV1.toP6W initial) =
    .ok (mapArray AspisR1S9CandidateHelperV1.toP6W output)
  dsimp only [p6step, AspisR1S9FactoredLoopBodyShapeV3.body] at hp6loop
  unfold AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop
  exact hp6loop

#print axioms candidate_helper_success_maps_to_p6_loop

end AspisR1S9CandidateHelperLoopMapV1
