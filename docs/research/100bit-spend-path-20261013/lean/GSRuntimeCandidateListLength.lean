import GSRuntimeInitialDistanceEncoderBridge

set_option autoImplicit false
namespace AspisWide.GSRuntimeCandidateListLength
open AspisWide.GSRuntimeInitialDistanceEncoderBridge
open AspisWide.InitialForwardEncoderBaseV9 AspisWideTower
open AspisPool.AlgorithmicCircleDecoderV7

theorem initialRuntimeCloseList_length_le_112
    (received : InitialWord WideExact) (candidates : List (List WideExact))
    (h : candidates.length ≤ 112) :
    (initialRuntimeCloseList received candidates).length ≤ 112 := by
  unfold initialRuntimeCloseList
  exact (List.length_filter_le _ _).trans
    ((List.length_filterMap_le _ _).trans h)

#print axioms initialRuntimeCloseList_length_le_112
end AspisWide.GSRuntimeCandidateListLength
