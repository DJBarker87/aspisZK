import S9CandidateHelperLoopMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S9CandidateTopHelperMapV1

open AspisR1S9CandidateHelperV1
open AspisR1S9CandidateBodyTermsV1
open AspisR1S9CandidateHelperLoopMapV1
open AspisR1S9CandidateFoldMapPrimitivesV1

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev CQ := AspisR1S9CandidateHelperV1.field.QM31
abbrev CW := AspisR1S9CandidateHelperV1.field.WideExact
abbrev PW := AspisR1S9HelperP6.field.WideExact
abbrev CArray := Array CW (4#usize)
abbrev PArray := Array PW (4#usize)

/-- The remaining active-body suffix obligation, parameterized by the same
external C1/C2 input array. -/
abbrev CandidateSuffixTransport (ap1 : CArray) :=
  ∀ (side : U) (iterNext : R) (weights : CArray)
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
      (AspisR1S9CandidateHelperV1.toP6Q q16) =
      .ok (AspisR1S9CandidateHelperLoopMapV1.mapCandidateFlow flow)

private theorem toP6W_zero :
    AspisR1S9CandidateHelperV1.toP6W AspisR1S9CandidateHelperV1.field.WideExact.ZERO =
      AspisR1S9HelperP6.field.WideExact.ZERO := by
  unfold AspisR1S9CandidateHelperV1.toP6W
    AspisR1S9CandidateHelperV1.toP6Q
    AspisR1S9CandidateHelperV1.toP6CM
    AspisR1S9CandidateHelperV1.toP6M
    AspisR1S9CandidateHelperV1.field.WideExact.ZERO
    AspisR1S9CandidateHelperV1.field.QM31.ZERO
    AspisR1S9HelperP6.field.WideExact.ZERO
    AspisR1S9HelperP6.field.QM31.ZERO
  rfl

private theorem map_initial_zero :
    mapArray AspisR1S9CandidateHelperV1.toP6W
      (Array.repeat 4#usize AspisR1S9CandidateHelperV1.field.WideExact.ZERO) =
    Array.repeat 4#usize AspisR1S9HelperP6.field.WideExact.ZERO := by
  apply Subtype.ext
  change List.map AspisR1S9CandidateHelperV1.toP6W
      (List.replicate (4#usize).val
        AspisR1S9CandidateHelperV1.field.WideExact.ZERO) =
    List.replicate (4#usize).val AspisR1S9HelperP6.field.WideExact.ZERO
  simp only [List.map_replicate, toP6W_zero]

/-- Lift the public generated candidate `factored_s2_libra_weights` call to
its same P6 wrapper result. The wrapper's actual zero-array initialization is
mapped field-by-field; the loop theorem supplies the same returned output.
The Rust Std/from_fn and frozen-source binding boundaries remain external.
-/
theorem candidate_top_success_maps_to_p6
    (ap0 ap1 : CArray) (extra : Array CQ (2#usize)) (output : CArray)
    (htop : _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights
      ap0 ap1 extra = .ok output)
    (hextra : ∀ (j : U) (x : CQ), Array.index_usize extra j = .ok x →
      AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
        (AspisR1S9CandidateHelperV1.toP6Q x))
    (hap1 : ∀ (j : U) (x : PW),
      Array.index_usize (mapArray AspisR1S9CandidateHelperV1.toP6W ap1) j = .ok x →
      AspisR1S9HighTermsTraceV1.canonicalW x)
    (hsuffix : CandidateSuffixTransport ap1) :
    @AspisR1S9HelperP6.weights.factored_s2_libra_weights
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
      (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
      (mapArray AspisR1S9CandidateHelperV1.toP6Q extra) =
      .ok (mapArray AspisR1S9CandidateHelperV1.toP6W output) := by
  let initial : CArray := Array.repeat 4#usize AspisR1S9CandidateHelperV1.field.WideExact.ZERO
  have hloop : _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop
      AspisR1S9CandidateTwoBodyCallsV1.start0 ap0 ap1 extra initial = .ok output := by
    unfold _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights at htop
    change _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop
      AspisR1S9CandidateTwoBodyCallsV1.start0 ap0 ap1 extra initial = .ok output at htop
    exact htop
  have hmapped := AspisR1S9CandidateHelperLoopMapV1.candidate_helper_success_maps_to_p6_loop
    ap0 ap1 extra initial output hloop hextra hap1 hsuffix
  dsimp only [initial] at hmapped
  rw [map_initial_zero] at hmapped
  unfold _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights
  change _root_.AspisR1S9HelperP6.weights.factored_s2_libra_weights_loop
    AspisR1S9CandidateTwoBodyCallsV1.start0
    (mapArray AspisR1S9CandidateHelperV1.toP6W ap0)
    (mapArray AspisR1S9CandidateHelperV1.toP6W ap1)
    (mapArray AspisR1S9CandidateHelperV1.toP6Q extra)
    (Array.repeat 4#usize AspisR1S9HelperP6.field.WideExact.ZERO) =
    .ok (mapArray AspisR1S9CandidateHelperV1.toP6W output)
  exact hmapped

#print axioms candidate_top_success_maps_to_p6

end AspisR1S9CandidateTopHelperMapV1
