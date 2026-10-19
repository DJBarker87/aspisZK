import GSRuntimeFinalDistanceEncoderBridge

set_option autoImplicit false
namespace AspisWide.GSRuntimeFinalCandidateListLength
open AspisWide.GSRuntimeFinalDistanceEncoderBridge
open AspisPool.AlgorithmicCircleDecoderV7 AspisWideTower

theorem finalRuntimeCloseList_length_le_112
    (received : FinalWord WideExact) (candidates : List (List WideExact))
    (h : candidates.length ≤ 112) :
    (finalRuntimeCloseList received candidates).length ≤ 112 := by
  unfold finalRuntimeCloseList
  exact (List.length_filter_le _ _).trans
    ((List.length_filterMap_le _ _).trans h)

#print axioms finalRuntimeCloseList_length_le_112
end AspisWide.GSRuntimeFinalCandidateListLength
