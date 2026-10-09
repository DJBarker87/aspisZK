import SelectedPoseidonBooleanPacking

/-! Exact active selector cases for the Boolean Poseidon source. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 4000

namespace AspisV8Completion.SelectedPoseidonActivePairs
open AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedNoteRecovery
open AspisV8.SelectedConcreteRowLanes
open AspisV8Completion.SelectedPoseidonGenericAlgebra
open AspisV8Completion.SelectedPoseidonBooleanPacking

abbrev F := M31Exact

theorem externalLinear_base :
    (SelectedPoseidonGenericAlgebra.externalLinear : State F → State F) =
      extLinear := rfl

theorem internalLinear_base_lane (state : State F) (lane : Fin 16) :
    SelectedPoseidonGenericAlgebra.internalLinear state lane =
      intLinear state lane := by
  fin_cases lane <;> rfl

theorem fullRound_base (state constants : State F) :
    SelectedPoseidonGenericAlgebra.fullRound state constants =
      extLinear (fullSbox constants state) := by
  unfold SelectedPoseidonGenericAlgebra.fullRound fullSbox
  rw [externalLinear_base]
  rfl

theorem internalRound_base (state : State F) (constant : F) :
    SelectedPoseidonGenericAlgebra.internalRound state constant =
      intLinear (intSbox constant state) := by
  funext lane
  unfold SelectedPoseidonGenericAlgebra.internalRound
  rw [internalLinear_base_lane]
  rfl

theorem baseSelector_active (block : Fin 57) (pair : Fin 11) (index : Fin 16) :
    baseSelector (poseidonRow block pair) index =
      if pair.val = index.val then 1 else 0 := by
  simp [baseSelector, poseidonRow]
  congr 2
  omega

theorem baseBlock_active (block : Fin 57) (pair : Fin 11) :
    baseBlock (poseidonRow block pair) = 1 := by
  simp [baseBlock, poseidonRow]
  omega

theorem baseTrace_zero (table : BaseTable) (block : Fin 57) (pair : Fin 11) :
    baseTrace table 0 (poseidonRow block pair) =
      state table (16 * block.val + pair.val) := by
  funext lane
  simp [baseTrace, viewRow, poseidonRow, state]

theorem baseTrace_successor (table : BaseTable) (block : Fin 57) (pair : Fin 11) :
    baseTrace table 1 (poseidonRow block pair) =
      pairState table block.val (pair.val + 1) := by
  funext lane
  simp [baseTrace, viewRow, poseidonRow, pairState, state]

theorem xor_block_row (block : Fin 57) :
    (16 * block.val) ^^^ 12 = 16 * block.val + 12 := by
  fin_cases block <;> decide

theorem absorbRate_pair_zero (table : BaseTable) (block : Fin 57) :
    absorbRate (baseTrace table 0 (poseidonRow block 0))
      (baseTrace table 2 (poseidonRow block 0)) = absorbed table block.val := by
  funext lane
  by_cases rate : lane.val < 8
  · simp [absorbRate, baseTrace, viewRow, poseidonRow, absorbed, absorb,
      state, chunk, rate]
    rw [xor_block_row]
  · simp [absorbRate, baseTrace, viewRow, poseidonRow, absorbed, absorb,
      state, chunk, rate]

theorem leadingPrediction_pair_zero (rc : RoundConstants) (table : BaseTable)
    (block : Fin 57) :
    leadingPrediction (RingHom.id F) rc
        (baseTrace table 0 (poseidonRow block 0))
        (baseTrace table 2 (poseidonRow block 0)) =
      gateStep rc 1 (gateStep rc 0 (pairState table block.val 0)) := by
  unfold leadingPrediction
  rw [absorbRate_pair_zero, externalLinear_base, fullRound_base, fullRound_base]
  simp [gateStep, poseidonRound, pairState]

theorem active_weights (block : Fin 57) (pair : Fin 11) :
    leadingWeight (baseSelector (poseidonRow block pair)) =
        (if pair.val = 0 then 1 else 0) ∧
      fullWeight (baseSelector (poseidonRow block pair)) =
        (if pair.val = 1 ∨ pair.val = 9 ∨ pair.val = 10 then 1 else 0) ∧
      internalWeight (baseSelector (poseidonRow block pair)) =
        (if 2 ≤ pair.val ∧ pair.val ≤ 8 then 1 else 0) := by
  fin_cases pair <;>
    simp [leadingWeight, fullWeight, internalWeight, baseSelector_active,
      Fin.sum_univ_succ] <;> decide

#print axioms baseSelector_active
#print axioms externalLinear_base
#print axioms internalLinear_base_lane
#print axioms fullRound_base
#print axioms internalRound_base
#print axioms baseBlock_active
#print axioms baseTrace_zero
#print axioms baseTrace_successor
#print axioms xor_block_row
#print axioms absorbRate_pair_zero
#print axioms leadingPrediction_pair_zero
#print axioms active_weights
end AspisV8Completion.SelectedPoseidonActivePairs
