import SelectedSemanticCallbackComposition
import SelectedSemanticPackedBoundary
import SourcePolynomialEndpointObstruction

/-! Exact 94-position ordering and positive-slot insertion for
`pair_forest_semantic_terminal::semantic_packed`.

The source appends the intervals 0..31, 32..48, 49..81, 82..83, 84..91,
and 92..93, then the repaired wrapper inserts position 94 in slot two of the
last pack. This file gives that order an explicit inverse into the selected
Boolean semantic-coordinate type and proves that packing those 94 Boolean
residual values, then inserting the positive residual, is exactly `packedRows`
and hence the `semanticMLE` lane used by the recovery-table model.

This does NOT identify the actual off-domain `semantic_packed` output with
that MLE: the source evaluates a degree-27 polynomial, and Boolean restriction
does not determine its off-domain value. The final theorem retains the
minimal Booleanity counterexample. Rust loop/memory refinement and a causal
source-polynomial trace remain separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000
set_option maxHeartbeats 1000000

namespace AspisV8Completion.SelectedSemanticPackedLiteral
open scoped BigOperators
open AspisFormal.ArithmetizationCore AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisV8.SelectedSemanticRows
open AspisPool.V7FixedWidth29TupleList
open AspisV8.EarlyC1LateProjection
open AspisV8.SelectedEarlyC1Amounts
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedConcreteRowLanes
open AspisV8.PositivePackBinding
open AspisV8.PositiveTerminalInsertion
open AspisV8Completion.SelectedSemanticCallbackComposition
open AspisV8Completion.SourcePolynomialEndpointObstruction

abbrev K := QM31Exact

/-- Literal inverse of the six contiguous ranges written by
`semantic_packed`; the positive coordinate is intentionally absent. -/
def sourceCoordinate94 (i : Fin 94) : Coordinate :=
  if h0 : i.val < 16 then .initial ⟨i.val, h0⟩
  else if h1 : i.val < 32 then .absorption ⟨i.val - 16, by omega⟩
  else if h2 : i.val = 32 then .direction
  else if h3 : i.val < 41 then .left ⟨i.val - 33, by omega⟩
  else if h4 : i.val < 49 then .right ⟨i.val - 41, by omega⟩
  else if h5 : i.val < 79 then .rangeBit ⟨i.val - 49, by omega⟩
  else if h6 : i.val = 79 then .recomposition
  else if h7 : i.val = 80 then .auxiliaryNext
  else if h8 : i.val = 81 then .auxiliaryXor
  else if h9 : i.val < 84 then .conservation ⟨i.val - 82, by omega⟩
  else if h10 : i.val < 92 then .digest ⟨i.val - 84, by omega⟩
  else .scalar ⟨i.val - 92, by omega⟩

theorem position_sourceCoordinate94 (i : Fin 94) :
    position (sourceCoordinate94 i) = i.val := by
  by_cases h0 : i.val < 16
  · simp [sourceCoordinate94, h0, position]
  by_cases h1 : i.val < 32
  · simp [sourceCoordinate94, h0, h1, position]
    omega
  by_cases h2 : i.val = 32
  · simp [sourceCoordinate94, h0, h1, h2, position]
  by_cases h3 : i.val < 41
  · simp [sourceCoordinate94, h0, h1, h2, h3, position]
    omega
  by_cases h4 : i.val < 49
  · simp [sourceCoordinate94, h0, h1, h2, h3, h4, position]
    omega
  by_cases h5 : i.val < 79
  · simp [sourceCoordinate94, h0, h1, h2, h3, h4, h5, position]
    omega
  by_cases h6 : i.val = 79
  · simp [sourceCoordinate94, h0, h1, h2, h3, h4, h5, h6, position]
  by_cases h7 : i.val = 80
  · simp [sourceCoordinate94, h0, h1, h2, h3, h4, h5, h6, h7, position]
  by_cases h8 : i.val = 81
  · simp [sourceCoordinate94, h0, h1, h2, h3, h4, h5, h6, h7, h8, position]
  by_cases h9 : i.val < 84
  · simp [sourceCoordinate94, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      position]
    omega
  by_cases h10 : i.val < 92
  · simp [sourceCoordinate94, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, position]
    omega
  · simp [sourceCoordinate94, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, position]
    omega

theorem packedLane_sourceCoordinate94 (i : Fin 94) :
    (packedLane (sourceCoordinate94 i)).val = i.val / 4 := by
  simp [packedLane, position_sourceCoordinate94]

theorem packedSlot_sourceCoordinate94 (i : Fin 94) :
    (packedSlot (sourceCoordinate94 i)).val = i.val % 4 := by
  simp [packedSlot, position_sourceCoordinate94]

/-- The 94 source-position values on one Boolean row before packing. -/
def sourceValue94 (pub : Public) (table : BaseTable) (row : Fin 1024)
    (i : Fin 94) : K :=
  liftBase (residual pub table (sourceCoordinate94 i) row.val)

theorem sourceValue94_eq_rows (pub : Public) (table : BaseTable)
    (row : Fin 1024) (i : Fin 94) :
    sourceValue94 pub table row i =
      liftBase (rows pub table row
        ⟨i.val / 4, by have := i.isLt; omega⟩
        ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩) := by
  unfold sourceValue94
  rw [← rows_at_coordinate pub table (sourceCoordinate94 i) row]
  congr 2
  · apply Fin.ext
    exact packedLane_sourceCoordinate94 i
  · apply Fin.ext
    exact packedSlot_sourceCoordinate94 i

/-- Boolean-table packing for positions 0..93. Slot 94 and structural slot95
are zero at this stage. This is not the off-domain Rust evaluator. -/
def semanticPacked94 (pub : Public) (table : BaseTable) (row : Fin 1024)
    (group : Fin 24) : K :=
  literalPack (fun slot =>
    if bounded : 4 * group.val + slot.val < 94 then
      sourceValue94 pub table row ⟨4 * group.val + slot.val, bounded⟩
    else 0)

theorem semanticPacked94_eq_packedRows_of_lt (pub : Public) (table : BaseTable)
    (row : Fin 1024) (group : Fin 24) (beforeLast : group.val < 23) :
    semanticPacked94 pub table row group = packedRows pub table row group := by
  unfold semanticPacked94 packedRows
  apply congrArg literalPack
  funext slot
  have bounded : 4 * group.val + slot.val < 94 := by
    have := slot.isLt
    omega
  rw [dif_pos bounded, sourceValue94_eq_rows]
  congr 3 <;> simp <;> omega

theorem rows_last_padding_zero (pub : Public) (table : BaseTable)
    (row : Fin 1024) : rows pub table row ⟨23, by decide⟩ ⟨3, by decide⟩ = 0 := by
  unfold rows
  apply Finset.sum_eq_zero
  intro coordinate _
  rw [if_neg]
  intro location
  have value := congrArg
    (fun pair : Fin 24 × Fin 4 => 4 * pair.1.val + pair.2.val) location
  rw [packedLocation, packed_recovers_position] at value
  have bound := position_lt coordinate
  simp at value
  omega

theorem semanticPacked94_last_slots (pub : Public) (table : BaseTable)
    (row : Fin 1024) :
    semanticPacked94 pub table row ⟨23, by decide⟩ =
      literalPack ![
        liftBase (rows pub table row ⟨23, by decide⟩ ⟨0, by decide⟩),
        liftBase (rows pub table row ⟨23, by decide⟩ ⟨1, by decide⟩),
        0, 0] := by
  unfold semanticPacked94
  congr 1
  funext slot
  fin_cases slot
  · rw [dif_pos (by decide), sourceValue94_eq_rows]
    rfl
  · rw [dif_pos (by decide), sourceValue94_eq_rows]
    rfl
  · rw [dif_neg (by decide)]
    rfl
  · rw [dif_neg (by decide)]
    rfl

/-- The repaired position 94 is precisely slot two of the last semantic
pack.  No other source output or padding slot changes. -/
theorem semanticPacked94_add_positive_eq_packedRows (pub : Public)
    (table : BaseTable) (row : Fin 1024) :
    semanticPacked94 pub table row ⟨23, by decide⟩ +
        literalPack ![0, 0, liftBase (residual pub table .positive row.val), 0] =
      packedRows pub table row ⟨23, by decide⟩ := by
  rw [semanticPacked94_last_slots]
  unfold packedRows
  have positive : rows pub table row ⟨23, by decide⟩ ⟨2, by decide⟩ =
      residual pub table .positive row.val := by
    rw [← rows_at_coordinate pub table Coordinate.positive row]
    rfl
  have padding := rows_last_padding_zero pub table row
  let base : Fin 4 → K := ![
    liftBase (rows pub table row ⟨23, by decide⟩ ⟨0, by decide⟩),
    liftBase (rows pub table row ⟨23, by decide⟩ ⟨1, by decide⟩), 0, 0]
  let added := liftBase (residual pub table .positive row.val)
  have inputs : (fun slot => liftBase (rows pub table row ⟨23, by decide⟩ slot)) =
      addSlot2 base added := by
    funext slot
    fin_cases slot
    · rfl
    · rfl
    · simpa [base, added, addSlot2] using congrArg liftBase positive
    · simpa [base, added, addSlot2, liftBase_zero] using congrArg liftBase padding
  rw [inputs]
  rw [literalPack_eq_tower_map, literalPack_eq_tower_map,
    literalPack_eq_tower_map]
  exact (pack_slot2_add towerI towerU base added).symm

/-- All 24 source packs after the positive insertion. -/
def semanticPacked95 (pub : Public) (table : BaseTable) (row : Fin 1024)
    (group : Fin 24) : K :=
  if group.val = 23 then
    semanticPacked94 pub table row group +
      literalPack ![0, 0, liftBase (residual pub table .positive row.val), 0]
  else semanticPacked94 pub table row group

theorem semanticPacked95_eq_packedRows (pub : Public) (table : BaseTable)
    (row : Fin 1024) (group : Fin 24) :
    semanticPacked95 pub table row group = packedRows pub table row group := by
  unfold semanticPacked95
  by_cases last : group.val = 23
  · rw [if_pos last]
    have same : group = ⟨23, by decide⟩ := Fin.ext last
    subst group
    exact semanticPacked94_add_positive_eq_packedRows pub table row
  · rw [if_neg last]
    exact semanticPacked94_eq_packedRows_of_lt pub table row group (by omega)

/-- MLE transport of the complete 24-pack equality.  Keeping the table
generic prevents elaboration from unfolding the much larger payment-candidate
record while proving the linear statement. -/
theorem semanticPacked95_MLE_eq_packedRowsMLE (pub : Public) (table : BaseTable)
    (point : Fin 10 → K) (group : Fin 24) :
    tableMLEValue point (fun row => semanticPacked95 pub table row group) =
      tableMLEValue point (fun row => packedRows pub table row group) := by
  unfold tableMLEValue
  apply Finset.sum_congr rfl
  intro row _
  change mleRowWeight point row *
      semanticPacked95 pub table row group =
    mleRowWeight point row * packedRows pub table row group
  rw [semanticPacked95_eq_packedRows]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
/-- Direct handoff to the Boolean-table semantic lane used by the composed
recovery model. This remains distinct from the off-domain Rust endpoint. -/
theorem semanticPacked95_MLE_eq_semanticMLE (pub : Public)
    (candidate : C1InitialMessages) (point : Fin 10 → K) (group : Fin 24) :
    tableMLEValue point (fun row =>
        semanticPacked95 pub (semanticTable candidate) row group) =
      semanticMLE pub candidate point group := by
  unfold semanticMLE
  exact semanticPacked95_MLE_eq_packedRowsMLE pub (semanticTable candidate) point group

set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
/-- The semantic projection currently used in the composed recovery model is
constructed by the 94-position Boolean writer plus positive insertion. -/
theorem callbackLanes_semantic_eq_boolean_writer (rc : RoundConstants) (pub : Public)
    (candidate : C1InitialMessages) (lambda chi helperAtPoint : K)
    (point : Fin 10 → K) (group : Fin 24) :
    (callbackLanes rc pub candidate lambda chi helperAtPoint point).semantic group =
      tableMLEValue point (fun row =>
        semanticPacked95 pub (semanticTable candidate) row group) := by
  change semanticMLE pub candidate point group = _
  exact (semanticPacked95_MLE_eq_semanticMLE pub candidate point group).symm

/-- Precise obstruction to upgrading the Boolean writer theorem to an actual
source endpoint: a source Booleanity term has zero Boolean table and therefore
zero table MLE, while remaining nonzero at an ordinary off-domain point. -/
theorem boolean_writer_does_not_determine_source_semantic
    (point : Fin 10 → K) (offDomain : firstCoordinateBooleanity point ≠ 0) :
    firstCoordinateBooleanity point ≠
      tableMLEValue point (zeroBooleanTable : Fin 1024 → K) :=
  booleanRestriction_does_not_fix_sourceEndpoint point offDomain

#print axioms position_sourceCoordinate94
#print axioms sourceValue94_eq_rows
#print axioms semanticPacked94_eq_packedRows_of_lt
#print axioms rows_last_padding_zero
#print axioms semanticPacked94_add_positive_eq_packedRows
#print axioms semanticPacked95_eq_packedRows
#print axioms semanticPacked95_MLE_eq_packedRowsMLE
#print axioms semanticPacked95_MLE_eq_semanticMLE
#print axioms callbackLanes_semantic_eq_boolean_writer
#print axioms boolean_writer_does_not_determine_source_semantic
end AspisV8Completion.SelectedSemanticPackedLiteral
