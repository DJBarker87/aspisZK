import SelectedPoseidonActiveResidual

/-! Complete Boolean-row restriction of the exact chronological Poseidon
source, followed by the selected four-coordinate tower packing.  This does
not assert refinement of the optimized Rust machine implementation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 4000

namespace AspisV8Completion.SelectedPoseidonAllRowsPacking
open AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.PositiveTerminalInsertion
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedNoteRecovery
open AspisV8.SelectedConcreteRowLanes
open AspisV8Completion.SelectedInitialOutputsSourcePolynomial
open AspisV8Completion.SelectedPoseidonCoordinateSlice
open AspisV8Completion.SelectedPoseidonBooleanPacking
open AspisV8Completion.SelectedPoseidonGenericAlgebra
open AspisV8Completion.SelectedPoseidonActiveResidual

abbrev K := QM31Exact
abbrev F := M31Exact

theorem inactive_pair_weights (row : Fin 1024) (inactive : ¬ row.val % 16 < 11) :
    leadingWeight (baseSelector row) = 0 ∧
      fullWeight (baseSelector row) = 0 ∧
      internalWeight (baseSelector row) = 0 := by
  have remainder : row.val % 16 < 16 := Nat.mod_lt _ (by decide)
  have h0 : row.val % 16 ≠ 0 := by omega
  have h1 : row.val % 16 ≠ 1 := by omega
  have h2 : row.val % 16 ≠ 2 := by omega
  have h3 : row.val % 16 ≠ 3 := by omega
  have h4 : row.val % 16 ≠ 4 := by omega
  have h5 : row.val % 16 ≠ 5 := by omega
  have h6 : row.val % 16 ≠ 6 := by omega
  have h7 : row.val % 16 ≠ 7 := by omega
  have h8 : row.val % 16 ≠ 8 := by omega
  have h9 : row.val % 16 ≠ 9 := by omega
  have h10 : row.val % 16 ≠ 10 := by omega
  have selector_zero (index : Fin 7) :
      baseSelector row ⟨index.val + 2, by omega⟩ = 0 := by
    simp [baseSelector]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp [leadingWeight, baseSelector, h0]
  · simp [fullWeight, baseSelector, h1, h9, h10]
  · simp [internalWeight, selector_zero]

theorem baseCoordinate_inactive_block (rc : RC) (table : BaseTable)
    (row : Fin 1024) (lane : Fin 16) (inactive : ¬ row.val / 16 < 57) :
    baseCoordinate rc table row lane = 0 := by
  simp [baseCoordinate, baseBlock, residualCoordinate, inactive]

theorem baseCoordinate_inactive_pair (rc : RC) (table : BaseTable)
    (row : Fin 1024) (lane : Fin 16) (inactive : ¬ row.val % 16 < 11) :
    baseCoordinate rc table row lane = 0 := by
  obtain ⟨leading, full, internal⟩ := inactive_pair_weights row inactive
  simp [baseCoordinate, residualCoordinate, leading, full, internal]

theorem baseCoordinate_eq_poseidonCoordinate (rc : RC) (table : BaseTable)
    (row : Fin 1024) (group slot : Fin 4) :
    baseCoordinate rc table row (stateLane group slot) =
      poseidonCoordinate rc table row group slot := by
  by_cases blockActive : row.val / 16 < 57
  · by_cases pairActive : row.val % 16 < 11
    · let block : Fin 57 := ⟨row.val / 16, blockActive⟩
      let pair : Fin 11 := ⟨row.val % 16, pairActive⟩
      have row_eq : row = poseidonRow block pair := by
        apply Fin.ext
        simp [poseidonRow, block, pair]
        omega
      rw [row_eq, baseCoordinate_active, poseidonCoordinate_active]
    · rw [baseCoordinate_inactive_pair rc table row (stateLane group slot) pairActive]
      simp [poseidonCoordinate, blockActive, pairActive]
  · rw [baseCoordinate_inactive_block rc table row (stateLane group slot) blockActive]
    simp [poseidonCoordinate, blockActive]

theorem coordinateValue_boolean_poseidon (rc : RC) (table : BaseTable)
    (row : Fin 1024) (group slot : Fin 4) :
    coordinateValue rc table (booleanTracePoint row) (stateLane group slot) =
      liftBase (poseidonCoordinate rc table row group slot) := by
  rw [coordinateValue_boolean_base, baseCoordinate_eq_poseidonCoordinate]

/-- Four actual source coordinates packed in the selected tower order. -/
def sourcePoseidonLane (rc : RC) (table : BaseTable)
    (point : Fin 10 → K) (group : Fin 4) : K :=
  literalPack (fun slot => coordinateValue rc table point (stateLane group slot))

theorem sourcePoseidonLane_boolean (rc : RC) (table : BaseTable)
    (row : Fin 1024) (group : Fin 4) :
    sourcePoseidonLane rc table (booleanTracePoint row) group =
      packedPoseidon rc table row group := by
  unfold sourcePoseidonLane packedPoseidon
  apply congrArg literalPack
  funext slot
  exact coordinateValue_boolean_poseidon rc table row group slot

#print axioms inactive_pair_weights
#print axioms baseCoordinate_inactive_block
#print axioms baseCoordinate_inactive_pair
#print axioms baseCoordinate_eq_poseidonCoordinate
#print axioms coordinateValue_boolean_poseidon
#print axioms sourcePoseidonLane_boolean
end AspisV8Completion.SelectedPoseidonAllRowsPacking
