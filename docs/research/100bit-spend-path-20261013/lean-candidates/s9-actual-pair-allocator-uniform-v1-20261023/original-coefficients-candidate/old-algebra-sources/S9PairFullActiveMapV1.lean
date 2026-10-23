import S9PairCallerActiveBodyMapV1
import S9PairCandidateAfterTermsMapV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S9PairFullActiveMapV1
open AspisR1S9PairCallerActiveBodyMapV1
open AspisR1S9PairCallerCandidateMapV1

theorem pair_active_body_maps_to_candidate
    (ap0 ap1 : PairArray)
    (extra : Array AspisR1S9PairCallerStepV1.field.QM31 (2#usize))
    (side : U) (iterNext : R) (weights : PairArray) :
    AspisR1S9CandidateFoldMapPrimitivesV1.mapResult pairToCandidateFlow
      (AspisR1S9PairCallerBodyPrefixV1.pairActiveBody
        ap0 ap1 extra side iterNext weights) =
    AspisR1S9CandidateBodyPrefixV1.candidateActiveBody
      (mapArray pairToCandidateW ap0) (mapArray pairToCandidateW ap1)
      (mapArray pairToCandidateQ extra) side iterNext
      (mapArray pairToCandidateW weights) := by
  apply pair_active_body_maps_to_candidate_of_after_low
  intro q41 q8 q12 q16 low
  exact AspisR1S9PairCandidateAfterTermsMapV1.pair_after_low_result_maps
    ap1 side iterNext weights q41 q8 q12 q16 low

#print axioms pair_active_body_maps_to_candidate
end AspisR1S9PairFullActiveMapV1
