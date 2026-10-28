import JGk_TX2_KeyInjective
import NDO_JGk_TX2_FrontierOrder
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGk_TX2_PositionsExact
open OraclePortSelectedDraft

def positions : List Nat := [21,17,15,19,18,10,13,14,12,16,20,11]
theorem members : ∀ a ∈ positions, a ∈ batchPositions 1 := by
  intro a ha
  simp only [positions,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
#print axioms members

theorem tree0 : OraclePortFrozenOrder.sortedPositions JGk_TX2_FrontierOrder.q 1 0=positions := by
  apply JGk_TX2_KeyInjective.source (batchPositions 1) _ _ JGk_TX2_Positions0.key
    JGk_TX2_Positions0.distinct
  · intro a ha
    exact List.mem_mergeSort.mp ha
  · exact members
  · exact JGk_TX2_Positions0.source
#print axioms tree0

theorem tree1 : OraclePortFrozenOrder.sortedPositions JGk_TX2_FrontierOrder.q 1 1=positions := by
  apply JGk_TX2_KeyInjective.source (batchPositions 1) _ _ JGk_TX2_Positions1.key
    JGk_TX2_Positions1.distinct
  · intro a ha
    exact List.mem_mergeSort.mp ha
  · exact members
  · exact JGk_TX2_Positions1.source
#print axioms tree1

theorem tree2 : OraclePortFrozenOrder.sortedPositions JGk_TX2_FrontierOrder.q 1 2=positions := by
  apply JGk_TX2_KeyInjective.source (batchPositions 1) _ _ JGk_TX2_Positions2.key
    JGk_TX2_Positions2.distinct
  · intro a ha
    exact List.mem_mergeSort.mp ha
  · exact members
  · exact JGk_TX2_Positions2.source
#print axioms tree2
end AspisR1.JGk_TX2_PositionsExact
end
