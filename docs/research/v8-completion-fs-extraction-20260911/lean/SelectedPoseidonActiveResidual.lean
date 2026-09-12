import SelectedPoseidonActivePairs

/-! Exact selected prediction and residual identities for all eleven active
Poseidon row classes.  This is still the mathematical source evaluator: the
literal optimized Rust loop/Aeneas refinement remains a separate boundary. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 4000

namespace AspisV8Completion.SelectedPoseidonActiveResidual
open AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedNoteRecovery
open AspisV8.SelectedConcreteRowLanes
open AspisV8Completion.SelectedPoseidonGenericAlgebra
open AspisV8Completion.SelectedPoseidonBooleanPacking
open AspisV8Completion.SelectedPoseidonActivePairs

abbrev F := M31Exact

theorem fullPrediction_one (rc : RoundConstants) (table : BaseTable)
    (block : Fin 57) :
    fullPrediction (RingHom.id F) rc
        (baseTrace table 0 (poseidonRow block 1))
        (baseSelector (poseidonRow block 1)) =
      gateStep rc 3 (gateStep rc 2 (pairState table block.val 1)) := by
  have even : fullEvenConstants (RingHom.id F) rc
      (baseSelector (poseidonRow block 1)) = rc.extInit 2 := by
    funext lane
    simp [fullEvenConstants, baseSelector_active]
  have odd : fullOddConstants (RingHom.id F) rc
      (baseSelector (poseidonRow block 1)) = rc.extInit 3 := by
    funext lane
    simp [fullOddConstants, baseSelector_active]
  unfold fullPrediction
  rw [even, odd, fullRound_base, fullRound_base, baseTrace_zero]
  simp [gateStep, poseidonRound, pairState]

theorem fullPrediction_nine (rc : RoundConstants) (table : BaseTable)
    (block : Fin 57) :
    fullPrediction (RingHom.id F) rc
        (baseTrace table 0 (poseidonRow block 9))
        (baseSelector (poseidonRow block 9)) =
      gateStep rc 19 (gateStep rc 18 (pairState table block.val 9)) := by
  have even : fullEvenConstants (RingHom.id F) rc
      (baseSelector (poseidonRow block 9)) = rc.extFinal 0 := by
    funext lane
    simp [fullEvenConstants, baseSelector_active]
  have odd : fullOddConstants (RingHom.id F) rc
      (baseSelector (poseidonRow block 9)) = rc.extFinal 1 := by
    funext lane
    simp [fullOddConstants, baseSelector_active]
  unfold fullPrediction
  rw [even, odd, fullRound_base, fullRound_base, baseTrace_zero]
  simp [gateStep, poseidonRound, pairState]

theorem fullPrediction_ten (rc : RoundConstants) (table : BaseTable)
    (block : Fin 57) :
    fullPrediction (RingHom.id F) rc
        (baseTrace table 0 (poseidonRow block 10))
        (baseSelector (poseidonRow block 10)) =
      gateStep rc 21 (gateStep rc 20 (pairState table block.val 10)) := by
  have even : fullEvenConstants (RingHom.id F) rc
      (baseSelector (poseidonRow block 10)) = rc.extFinal 2 := by
    funext lane
    simp [fullEvenConstants, baseSelector_active]
  have odd : fullOddConstants (RingHom.id F) rc
      (baseSelector (poseidonRow block 10)) = rc.extFinal 3 := by
    funext lane
    simp [fullOddConstants, baseSelector_active]
  unfold fullPrediction
  rw [even, odd, fullRound_base, fullRound_base, baseTrace_zero]
  simp [gateStep, poseidonRound, pairState]

theorem internalPrediction_active (rc : RoundConstants) (table : BaseTable)
    (block : Fin 57) (pair : Fin 11)
    (internal : 2 ≤ pair.val ∧ pair.val ≤ 8) :
    internalPrediction (RingHom.id F) rc
        (baseTrace table 0 (poseidonRow block pair))
        (baseSelector (poseidonRow block pair)) =
      gateStep rc (2 * pair.val + 1)
        (gateStep rc (2 * pair.val) (pairState table block.val pair.val)) := by
  fin_cases pair <;>
    simp at internal ⊢
  all_goals
    unfold internalPrediction
    rw [internalRound_base, internalRound_base]
    simp [internalEvenConstant, internalOddConstant, baseSelector_active,
      baseTrace_zero, gateStep, poseidonRound, pairState, Fin.sum_univ_succ]

theorem baseCoordinate_active (rc : RoundConstants) (table : BaseTable)
    (block : Fin 57) (pair : Fin 11) (lane : Fin 16) :
    baseCoordinate rc table (poseidonRow block pair) lane =
      pairResidual rc table block pair lane := by
  fin_cases pair
  · simp [baseCoordinate, residualCoordinate, pairResidual, baseBlock_active,
      baseTrace_successor, active_weights, leadingPrediction_pair_zero]
  · simp [baseCoordinate, residualCoordinate, pairResidual, baseBlock_active,
      baseTrace_successor, active_weights, fullPrediction_one]
  all_goals
    simp [baseCoordinate, residualCoordinate, pairResidual, baseBlock_active,
      baseTrace_successor, active_weights, internalPrediction_active,
      fullPrediction_nine, fullPrediction_ten]

#print axioms fullPrediction_one
#print axioms fullPrediction_nine
#print axioms fullPrediction_ten
#print axioms internalPrediction_active
#print axioms baseCoordinate_active
end AspisV8Completion.SelectedPoseidonActiveResidual
