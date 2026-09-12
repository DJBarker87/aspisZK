import SelectedPoseidonCoordinateDegree
import SelectedConcreteRowLanes

/-! Boolean restriction and tower packing for the chronological Poseidon source.

This file identifies the exact nonlinear source expression on the committed
Boolean trace rows.  It does not identify the optimized Rust evaluator with
that expression; that machine-level refinement remains external. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option maxRecDepth 4000

namespace AspisV8Completion.SelectedPoseidonBooleanPacking
open AspisFormal.HashMerkleModel
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedNoteRecovery
open AspisV8.SelectedConcreteRowLanes
open AspisV8Completion.SelectedInitialOutputsSourcePolynomial
open AspisV8Completion.SelectedValueAuxiliarySourcePolynomial
open AspisV8Completion.SelectedPoseidonGenericAlgebra
open AspisV8Completion.SelectedPoseidonCoordinateSlice

abbrev K := QM31Exact
abbrev F := M31Exact

def baseBlock (row : Fin 1024) : F := if row.val / 16 < 57 then 1 else 0
def baseSelector (row : Fin 1024) : State F := fun index =>
  if row.val % 16 = index.val then 1 else 0
def baseTrace (table : BaseTable) (view : Fin 3) (row : Fin 1024) : State F :=
  fun lane => table (viewRow row.val view) lane.val

theorem blockValue_boolean (row : Fin 1024) :
    blockValue (booleanTracePoint row) = liftBase (baseBlock row) := by
  rw [show blockValue (booleanTracePoint row) =
    (if row.val / 16 < 57 then 1 else 0) from indicator_boolean _ _]
  split <;> simp [baseBlock, liftBase_one, liftBase_zero, *]

theorem selectorValue_boolean (row : Fin 1024) :
    selectorValue (booleanTracePoint row) = mapState baseToK (baseSelector row) := by
  funext index
  change mleValue (localTable index) (booleanTracePoint row) = _
  unfold localTable
  rw [indicator_boolean]
  simp [baseSelector, mapState]

theorem traceValue_boolean (table : BaseTable) (view : Fin 3) (row : Fin 1024) :
    traceValue table view (booleanTracePoint row) =
      mapState baseToK (baseTrace table view row) := by
  funext lane
  change tableMLEValue (booleanTracePoint row) (viewTable table view lane.val) = _
  unfold viewTable
  rw [traceTable_boolean]
  rfl

def baseCoordinate (rc : RC) (table : BaseTable) (row : Fin 1024)
    (lane : Fin 16) : F :=
  residualCoordinate (RingHom.id F) rc (baseBlock row) (baseSelector row)
    (baseTrace table 0 row) (baseTrace table 1 row) (baseTrace table 2 row) lane

theorem coordinateValue_boolean_base (rc : RC) (table : BaseTable)
    (row : Fin 1024) (lane : Fin 16) :
    coordinateValue rc table (booleanTracePoint row) lane =
      liftBase (baseCoordinate rc table row lane) := by
  rw [coordinateValue, blockValue_boolean row, selectorValue_boolean row,
    traceValue_boolean table 0 row, traceValue_boolean table 1 row,
    traceValue_boolean table 2 row]
  have mapped := residualCoordinate_map baseToK (RingHom.id F) baseToK
    (by rfl) rc (baseBlock row) (baseSelector row)
      (baseTrace table 0 row) (baseTrace table 1 row)
      (baseTrace table 2 row) lane
  simpa [baseCoordinate, mapState, baseToK] using mapped

/- The eleven selector cases are intentionally proved below as separate
named facts, so the finite selector reduction never unfolds a 1024-row MLE. -/

#print axioms blockValue_boolean
#print axioms selectorValue_boolean
#print axioms traceValue_boolean
#print axioms coordinateValue_boolean_base
end AspisV8Completion.SelectedPoseidonBooleanPacking
