import SelectedCompleteSemanticSourcePolynomial
import SelectedSemanticCallbackComposition

/-! Exact packing of the 95 chronological semantic coordinate sources.

The arbitrary-point value here is the selected source-polynomial evaluation,
not the multilinear extension of its Boolean restriction.  Those coincide on
Boolean rows.  The general off-domain equality with `semanticMLE` is false as
an inference from Boolean tables (see `SourcePolynomialEndpointObstruction`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 3000

namespace AspisV8Completion.SelectedCompleteSemanticPackedSource
open scoped BigOperators
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.PositiveTerminalInsertion
open AspisV8.SelectedEarlyC1Amounts
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisPool.V7FixedWidth29TupleList
open AspisV8Completion.BooleanSuffixSourceConstructor
open AspisV8Completion.SelectedCompleteSemanticSourcePolynomial
open AspisV8Completion.SelectedSemanticCallbackComposition

abbrev K := QM31Exact

theorem indexedSpec_coordinateIndex (pub : Public) (table : BaseTable)
    (coordinate : Coordinate) :
    indexedSpec pub table (coordinateIndex coordinate) =
      coordinateSpec pub table coordinate := by
  unfold indexedSpec
  rw [show coordinateIndex coordinate = coordinateIndexEquiv coordinate by rfl]
  rw [Equiv.symm_apply_apply]

/-- The four base-coordinate source values belonging to one selected packed
lane.  The `if` is the exact selected position/slot map; position 95 has no
coordinate and therefore remains structural zero. -/
noncomputable def sourceRowsAtPoint (pub : Public) (table : BaseTable)
    (point : Fin 10 → K) (group : Fin 24) (slot : Fin 4) : K :=
  ∑ coordinate : Coordinate,
    if packedLocation coordinate = (group, slot) then
      (indexedSpec pub table (coordinateIndex coordinate)).value point
    else 0

/-- All 24 selected semantic lanes at an arbitrary point, packed from the 95
independently constructed chronological source polynomials. -/
noncomputable def sourceSemanticLanes (pub : Public) (table : BaseTable)
    (point : Fin 10 → K) (group : Fin 24) : K :=
  literalPack (sourceRowsAtPoint pub table point group)

theorem sourceRowsAtPoint_boolean (pub : Public) (table : BaseTable)
    (row : Fin 1024) (group : Fin 24) (slot : Fin 4) :
    sourceRowsAtPoint pub table (booleanTracePoint row) group slot =
      liftBase (rows pub table row group slot) := by
  unfold sourceRowsAtPoint rows
  rw [SelectedPublicOutputsSourcePolynomial.liftBase_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  by_cases location : packedLocation coordinate = (group, slot)
  · rw [if_pos location, if_pos location, indexedSpec_coordinateIndex]
    exact coordinateSpec_boolean_eq_literal pub table coordinate row
  · simp [location, liftBase_zero]

theorem sourceSemanticLanes_boolean (pub : Public) (table : BaseTable)
    (row : Fin 1024) (group : Fin 24) :
    sourceSemanticLanes pub table (booleanTracePoint row) group =
      packedRows pub table row group := by
  unfold sourceSemanticLanes packedRows
  apply congrArg literalPack
  funext slot
  exact sourceRowsAtPoint_boolean pub table row group slot

/-- The source-polynomial lanes and the older Boolean-table MLE agree on the
Boolean cube.  No arbitrary-point equality is asserted. -/
theorem sourceSemanticLanes_eq_semanticMLE_boolean (pub : Public)
    (candidate : C1InitialMessages) (row : Fin 1024) (group : Fin 24) :
    sourceSemanticLanes pub (semanticTable candidate) (booleanTracePoint row) group =
      semanticMLE pub candidate (booleanTracePoint row) group := by
  rw [sourceSemanticLanes_boolean]
  unfold semanticMLE
  symm
  exact tableMLEValue_booleanTracePoint
    (fun selected => packedRows pub (semanticTable candidate) selected group) row

/-- Source-level semantic field for the callback.  This is the replacement
interface required for a genuine off-domain source callback; it is constructed
at every point and has no acceptance or callback-equality premise. -/
noncomputable def sourceSemanticField (pub : Public) (candidate : C1InitialMessages)
    (point : Fin 10 → K) : Fin 24 → K :=
  sourceSemanticLanes pub (semanticTable candidate) point

theorem sourceSemanticField_boolean (pub : Public) (candidate : C1InitialMessages)
    (row : Fin 1024) :
    sourceSemanticField pub candidate (booleanTracePoint row) =
      fun group => semanticMLE pub candidate (booleanTracePoint row) group := by
  funext group
  exact sourceSemanticLanes_eq_semanticMLE_boolean pub candidate row group

#print axioms indexedSpec_coordinateIndex
#print axioms sourceRowsAtPoint_boolean
#print axioms sourceSemanticLanes
#print axioms sourceSemanticLanes_boolean
#print axioms sourceSemanticLanes_eq_semanticMLE_boolean
#print axioms sourceSemanticField_boolean
end AspisV8Completion.SelectedCompleteSemanticPackedSource
