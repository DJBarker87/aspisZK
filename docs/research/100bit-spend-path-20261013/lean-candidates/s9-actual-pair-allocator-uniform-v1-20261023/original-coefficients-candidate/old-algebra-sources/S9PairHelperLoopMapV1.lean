import S9PairTwoBodyCallsV1
import S9PairFullActiveMapV1
import S9CandidateBodyPrefixV1
import S9CandidateTwoBodyCallsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow

namespace AspisR1S9PairHelperLoopMapV4

abbrev U := Std.Usize
abbrev R := core.ops.range.Range U
abbrev PairW := Array AspisR1S9PairCallerStepV1.field.WideExact (4#usize)
abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev CandidateW := Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize)

abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

/-- Pair's generated loop result maps to the candidate loop result. The
same-call active-body map and the two successful Pair loop iterations are
composed to preserve the returned intermediate and final arrays. -/
theorem pair_helper_success_maps_to_candidate
    (ap0 ap1 : PairW) (extra : Array PairQ (2#usize))
    (initial output : PairW)
    (hloop : _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop
      AspisR1S9PairTwoBodyCallsV1.start0 ap0 ap1 extra initial = .ok output)
 :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW)
      (_root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights_loop
        AspisR1S9PairTwoBodyCallsV1.start0 ap0 ap1 extra initial) =
    _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop
      AspisR1S9CandidateTwoBodyCallsV1.start0
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW initial) := by
  obtain ⟨iter1, iter2, middle, hnext0, _, _, hbody0,
    hnext1, _, _, hbody1, hnext2, hbody2⟩ :=
    AspisR1S9PairTwoBodyCallsV1.helper_success_two_body_calls
      ap0 ap1 extra initial output hloop
  have hcbody0 :
      _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
        AspisR1S9PairTwoBodyCallsV1.start0
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW initial) =
      .ok (.cont (iter1, mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW middle)) := by
    have hactive := AspisR1S9PairFullActiveMapV1.pair_active_body_maps_to_candidate
      ap0 ap1 extra 0#usize iter1 initial
    have hpactive : AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
        ap0 ap1 extra 0#usize iter1 initial = .ok (.cont (iter1, middle)) := by
      rw [← AspisR1S9PairCallerBodyPrefixV1.body_some_eq_pairActiveBody
        ap0 ap1 extra AspisR1S9PairTwoBodyCallsV1.start0 iter1 0#usize initial hnext0]
      exact hbody0
    rw [hpactive] at hactive
    have hcactive : AspisR1S9CandidateBodyPrefixV1.candidateActiveBody
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
        0#usize iter1 (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW initial) =
      .ok (.cont (iter1, mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW middle)) := by
      simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult,
        AspisR1S9PairCallerActiveBodyMapV1.mapArray,
        AspisR1S9PairCallerActiveBodyMapV1.pairToCandidateFlow] using hactive.symm
    rw [AspisR1S9CandidateBodyPrefixV1.body_some_eq_candidateActiveBody
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
      AspisR1S9PairTwoBodyCallsV1.start0 iter1 0#usize
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW initial) hnext0]
    exact hcactive
  have hcbody1 :
      _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
        iter1 (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW middle) =
      .ok (.cont (iter2, mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW output)) := by
    have hactive := AspisR1S9PairFullActiveMapV1.pair_active_body_maps_to_candidate
      ap0 ap1 extra iter1.start iter2 middle
    have hpactive : AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
        ap0 ap1 extra iter1.start iter2 middle = .ok (.cont (iter2, output)) := by
      rw [← AspisR1S9PairCallerBodyPrefixV1.body_some_eq_pairActiveBody
        ap0 ap1 extra iter1 iter2 iter1.start middle hnext1]
      exact hbody1
    rw [hpactive] at hactive
    have hcactive : AspisR1S9CandidateBodyPrefixV1.candidateActiveBody
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
        iter1.start iter2 (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW middle) =
      .ok (.cont (iter2, mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW output)) := by
      simpa [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult,
        AspisR1S9PairCallerActiveBodyMapV1.mapArray,
        AspisR1S9PairCallerActiveBodyMapV1.pairToCandidateFlow] using hactive.symm
    rw [AspisR1S9CandidateBodyPrefixV1.body_some_eq_candidateActiveBody
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
      iter1 iter2 iter1.start
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW middle) hnext1]
    exact hcactive
  have hcbody2 :
      _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra)
        iter2 (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW output) =
      .ok (.done (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW output)) := by
    unfold _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
    rw [hnext2]
    rfl
  have hcloop : Aeneas.Std.loop
      (fun s => _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop.body
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
        (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra) s.1 s.2)
      (AspisR1S9PairTwoBodyCallsV1.start0,
        mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW initial) =
      .ok (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW output) := by
    rw [Aeneas.Std.loop.eq_def, hcbody0]
    simp only [bind_tc_ok]
    rw [Aeneas.Std.loop.eq_def, hcbody1]
    simp only [bind_tc_ok]
    rw [Aeneas.Std.loop.eq_def, hcbody2]
  rw [hloop]
  simp only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult]
  simpa only [AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights_loop,
    AspisR1S9PairTwoBodyCallsV1.start0, AspisR1S9CandidateTwoBodyCallsV1.start0] using hcloop.symm

#print axioms pair_helper_success_maps_to_candidate
end AspisR1S9PairHelperLoopMapV4
