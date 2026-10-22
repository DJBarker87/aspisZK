import S9PairHelperLoopMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairTopWrapperMapV1

abbrev PairW := Array AspisR1S9PairCallerStepV1.field.WideExact (4#usize)
abbrev PairQ := AspisR1S9PairCallerStepV1.field.QM31
abbrev CandidateW := Array AspisR1S9CandidateHelperV1.field.WideExact (4#usize)

abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

private theorem pair_zero_maps_candidate :
    AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
      AspisR1S9PairCallerStepV1.field.WideExact.ZERO =
    AspisR1S9CandidateHelperV1.field.WideExact.ZERO := by
  simp [AspisR1S9PairCallerCandidateMapV1.pairToCandidateW,
    AspisR1S9PairCallerStepV1.toP6W,
    AspisR1S9CandidateHelperV1.fromP6W,
    AspisR1S9PairCallerStepV1.field.WideExact.ZERO,
    AspisR1S9CandidateHelperV1.field.WideExact.ZERO,
    AspisR1S9PairCallerStepV1.field.QM31.ZERO,
    AspisR1S9CandidateHelperV1.field.QM31.ZERO,
    AspisR1S9PairCallerStepV1.toP6Q,
    AspisR1S9CandidateHelperV1.fromP6Q,
    AspisR1S9PairCallerStepV1.toP6CM,
    AspisR1S9CandidateHelperV1.fromP6CM,
    AspisR1S9PairCallerStepV1.toP6M,
    AspisR1S9CandidateHelperV1.fromP6M]

private theorem pair_initial_zero_maps_candidate :
    mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW
      (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO) =
    Array.repeat 4#usize AspisR1S9CandidateHelperV1.field.WideExact.ZERO := by
  simp [mapArray, AspisR1S9CandidateFoldMapPrimitivesV1.mapArray,
    pair_zero_maps_candidate]
  rfl

/-- The Pair top wrapper's successful output is preserved by the generated
helper map. This theorem is success-conditional: the Pair top call must return
`output`; it does not assert fail/div totality. -/
theorem pair_top_success_maps_to_candidate
    (ap0 ap1 : PairW) (extra : Array PairQ (2#usize)) (output : PairW)
    (hpair : _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights
      ap0 ap1 extra = .ok output) :
    _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap0)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW ap1)
      (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateQ extra) =
      .ok (mapArray AspisR1S9PairCallerCandidateMapV1.pairToCandidateW output) := by
  unfold _root_.AspisR1S9PairCallerStepV1.weights.factored_s2_libra_weights at hpair
  simp only [bind_tc_ok] at hpair
  have hloop := AspisR1S9PairHelperLoopMapV4.pair_helper_success_maps_to_candidate
    ap0 ap1 extra
    (Array.repeat 4#usize AspisR1S9PairCallerStepV1.field.WideExact.ZERO)
    output hpair
  dsimp only [AspisR1S9PairTwoBodyCallsV1.start0,
    AspisR1S9CandidateTwoBodyCallsV1.start0,
    AspisR1S9PairHelperLoopMapV4.mapArray] at hloop
  rw [hpair] at hloop
  simp only [AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] at hloop
  unfold _root_.AspisR1S9CandidateHelperV1.weights.factored_s2_libra_weights
  simp only [bind_tc_ok]
  rw [← pair_initial_zero_maps_candidate]
  exact hloop.symm

#print axioms pair_top_success_maps_to_candidate
end AspisR1S9PairTopWrapperMapV1
