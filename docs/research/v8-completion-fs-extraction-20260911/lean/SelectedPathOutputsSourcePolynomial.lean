import SelectedRecompositionRustShaped

/-! Chronological source polynomials for the seventeen selected path outputs.

The source expressions use the exact direction, left and right opening
indices and producer-minus-consumer signs of `path_lanes_literal`.  The path
selector is defined as the MLE of the literal Boolean `pathMask`; connecting
the Rust high/low factorisation that computes this same selector is kept as a
separate machine/source optimisation seam. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 2500

namespace AspisV8Completion.SelectedPathOutputsSourcePolynomial
open Polynomial
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.BooleanSuffixSourceConstructor
open AspisV8Completion.BooleanSuffixSourceAlgebra
open AspisV8Completion.SelectedValueAuxiliarySourcePolynomial
open AspisV8Completion.SelectedRecompositionRustShaped

abbrev K := QM31Exact

def pathIndicator : Fin 1024 → K := fun row =>
  if pathMask row.val then 1 else 0

def pathSelectorValue (point : Fin 10 → K) : K :=
  tableMLEValue point pathIndicator

noncomputable def pathSelectorSlice (fixed : Fin 10 → K)
    (round : Fin 10) : K[X] := openingSlice pathIndicator fixed round

theorem pathSelectorSlice_degree (fixed : Fin 10 → K) (round : Fin 10) :
    (pathSelectorSlice fixed round).natDegree ≤ 1 :=
  openingSlice_degree pathIndicator fixed round

theorem pathSelectorSlice_eval_at (fixed : Fin 10 → K)
    (round : Fin 10) (x : K) :
    (pathSelectorSlice fixed round).eval x =
      pathSelectorValue (replaceCoordinate fixed round x) :=
  openingSlice_eval_at pathIndicator fixed round x

inductive Output where
  | direction
  | left (limb : Fin 8)
  | right (limb : Fin 8)
  deriving DecidableEq, Fintype

def outputCoordinate : Output → Coordinate
  | .direction => .direction
  | .left limb => .left limb
  | .right limb => .right limb

def pathValue (table : BaseTable) (point : Fin 10 → K) : Output → K
  | .direction => pathSelectorValue point *
      tableMLEValue point (traceTable table 0 0) *
        (tableMLEValue point (traceTable table 0 0) - 1)
  | .left limb => pathSelectorValue point *
      (1 - tableMLEValue point (traceTable table 0 0)) *
        (tableMLEValue point (traceTable table 1 limb.val) -
          tableMLEValue point (traceTable table 0 (1 + limb.val)))
  | .right limb => pathSelectorValue point *
      tableMLEValue point (traceTable table 0 0) *
        (tableMLEValue point (traceTable table 1 (8 + limb.val)) -
          tableMLEValue point (traceTable table 0 (1 + limb.val)))

noncomputable def pathSlice (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) : Output → K[X]
  | .direction => pathSelectorSlice fixed round *
      openingSlice (traceTable table 0 0) fixed round *
        (openingSlice (traceTable table 0 0) fixed round - 1)
  | .left limb => pathSelectorSlice fixed round *
      (1 - openingSlice (traceTable table 0 0) fixed round) *
        (openingSlice (traceTable table 1 limb.val) fixed round -
          openingSlice (traceTable table 0 (1 + limb.val)) fixed round)
  | .right limb => pathSelectorSlice fixed round *
      openingSlice (traceTable table 0 0) fixed round *
        (openingSlice (traceTable table 1 (8 + limb.val)) fixed round -
          openingSlice (traceTable table 0 (1 + limb.val)) fixed round)

theorem pathSlice_degree (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (output : Output) :
    (pathSlice table fixed round output).natDegree ≤ 27 := by
  have selector := pathSelectorSlice_degree fixed round
  have bit := openingSlice_degree (traceTable table 0 0) fixed round
  cases output with
  | direction =>
      apply natDegree_mul_le.trans
      exact (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add selector bit))
        ((natDegree_sub_le _ _).trans (max_le bit (by simp)))).trans (by omega)
  | left limb =>
      have successor := openingSlice_degree (traceTable table 1 limb.val) fixed round
      have current := openingSlice_degree
        (traceTable table 0 (1 + limb.val)) fixed round
      apply natDegree_mul_le.trans
      exact (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add selector
          ((natDegree_sub_le _ _).trans (max_le (by simp) bit))))
        ((natDegree_sub_le _ _).trans (max_le successor current))).trans (by omega)
  | right limb =>
      have successor := openingSlice_degree
        (traceTable table 1 (8 + limb.val)) fixed round
      have current := openingSlice_degree
        (traceTable table 0 (1 + limb.val)) fixed round
      apply natDegree_mul_le.trans
      exact (Nat.add_le_add
        (natDegree_mul_le.trans (Nat.add_le_add selector bit))
        ((natDegree_sub_le _ _).trans (max_le successor current))).trans (by omega)

set_option maxRecDepth 10000 in
theorem pathSlice_eval_at (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (x : K) (output : Output) :
    (pathSlice table fixed round output).eval x =
      pathValue table (replaceCoordinate fixed round x) output := by
  cases output with
  | direction =>
      change (pathSelectorSlice fixed round *
          openingSlice (traceTable table 0 0) fixed round *
            (openingSlice (traceTable table 0 0) fixed round - 1)).eval x = _
      rw [eval_mul, eval_mul, eval_sub, eval_one, pathSelectorSlice_eval_at,
        openingSlice_eval_at]
      rfl
  | left limb =>
      change (pathSelectorSlice fixed round *
          (1 - openingSlice (traceTable table 0 0) fixed round) *
            (openingSlice (traceTable table 1 limb.val) fixed round -
              openingSlice (traceTable table 0 (1 + limb.val)) fixed round)).eval x = _
      rw [eval_mul, eval_mul, eval_sub, eval_sub, eval_one,
        pathSelectorSlice_eval_at, openingSlice_eval_at, openingSlice_eval_at,
        openingSlice_eval_at]
      rfl
  | right limb =>
      change (pathSelectorSlice fixed round *
          openingSlice (traceTable table 0 0) fixed round *
            (openingSlice (traceTable table 1 (8 + limb.val)) fixed round -
              openingSlice (traceTable table 0 (1 + limb.val)) fixed round)).eval x = _
      rw [eval_mul, eval_mul, eval_sub, pathSelectorSlice_eval_at,
        openingSlice_eval_at, openingSlice_eval_at, openingSlice_eval_at]
      rfl

set_option maxRecDepth 5000 in
noncomputable def outputSpec (table : BaseTable) (output : Output) :
    CoordinateSlices (K := K) where
  value := fun point => pathValue table point output
  slice := fun fixed round => pathSlice table fixed round output
  degree := fun fixed round => pathSlice_degree table fixed round output
  eval_at := fun fixed round x => pathSlice_eval_at table fixed round x output

noncomputable def source (table : BaseTable) (output : Output) :
    SourcePolynomial (booleanTable (outputSpec table output)) :=
  BooleanSuffixSourceConstructor.source (outputSpec table output)

theorem pathSelectorValue_boolean (row : Fin 1024) :
    pathSelectorValue (booleanTracePoint row) =
      if pathMask row.val then 1 else 0 := by
  exact tableMLEValue_booleanTracePoint _ _

theorem directionValue_boolean (table : BaseTable) (row : Fin 1024) :
    pathValue table (booleanTracePoint row) .direction =
      liftBase (directionResidual table row.val) := by
  simp only [pathValue]
  unfold directionResidual gate
  rw [pathSelectorValue_boolean, traceTable_boolean]
  simp only [viewRow]
  by_cases active : pathMask row.val
  · simp [active, liftBase_mul, liftBase_sub, liftBase_one]
  · simp [active, liftBase_zero]

theorem leftValue_boolean (table : BaseTable) (row : Fin 1024) (limb : Fin 8) :
    pathValue table (booleanTracePoint row) (.left limb) =
      liftBase (leftResidual table row.val limb) := by
  simp only [pathValue]
  unfold leftResidual gate
  rw [pathSelectorValue_boolean, traceTable_boolean, traceTable_boolean,
    traceTable_boolean]
  simp only [viewRow, Fin.val_zero]
  by_cases active : pathMask row.val
  · simp [active, liftBase_mul, liftBase_sub, liftBase_one]
  · simp [active, liftBase_zero]

theorem rightValue_boolean (table : BaseTable) (row : Fin 1024) (limb : Fin 8) :
    pathValue table (booleanTracePoint row) (.right limb) =
      liftBase (rightResidual table row.val limb) := by
  simp only [pathValue]
  unfold rightResidual gate
  rw [pathSelectorValue_boolean, traceTable_boolean, traceTable_boolean,
    traceTable_boolean]
  simp only [viewRow, Fin.val_zero]
  by_cases active : pathMask row.val
  · simp [active, liftBase_mul, liftBase_sub]
  · simp [active, liftBase_zero]

theorem booleanTable_eq_literal_residual (pub : Public) (table : BaseTable)
    (output : Output) (row : Fin 1024) :
    booleanTable (outputSpec table output) row =
      liftBase (residual pub table (outputCoordinate output) row.val) := by
  change pathValue table (booleanTracePoint row) output = _
  cases output with
  | direction => exact directionValue_boolean table row
  | left limb => exact leftValue_boolean table row limb
  | right limb => exact rightValue_boolean table row limb

/-- Independent array-level execution of the literal path formulas.  Its
selector input is the already-defined literal path-mask functional; the Rust
high/low selector factorisation remains a separate refinement obligation. -/
def rustPathOutput (selector : K) (z successor : RustArray) : Output → K
  | .direction => selector * z 0 * (z 0 - 1)
  | .left limb => selector * (1 - z 0) * (successor ⟨limb.val, by omega⟩ -
      z ⟨1 + limb.val, by omega⟩)
  | .right limb => selector * z 0 *
      (successor ⟨8 + limb.val, by omega⟩ - z ⟨1 + limb.val, by omega⟩)

theorem openingArray_at (table : BaseTable) (point : Fin 10 → K)
    (view : Fin 3) (column : Fin 16) :
    openingArray table point view column =
      tableMLEValue point (traceTable table view column.val) := by
  rfl

set_option maxRecDepth 10000 in
theorem rustPathOutput_eq_sourceValue (table : BaseTable) (point : Fin 10 → K)
    (output : Output) :
    rustPathOutput (pathSelectorValue point) (openingArray table point 0)
        (openingArray table point 1) output =
      (outputSpec table output).value point := by
  change rustPathOutput (pathSelectorValue point) (openingArray table point 0)
      (openingArray table point 1) output = pathValue table point output
  cases output with
  | direction =>
      simp only [rustPathOutput, pathValue]
      rw [openingArray_at]
      simp only [Fin.val_zero]
  | left limb =>
      simp only [rustPathOutput, pathValue]
      rw [openingArray_at, openingArray_at, openingArray_at]
      simp only [Fin.val_zero]
  | right limb =>
      simp only [rustPathOutput, pathValue]
      rw [openingArray_at, openingArray_at, openingArray_at]
      simp only [Fin.val_zero]

theorem source_initial_is_literal_residual (pub : Public) (table : BaseTable)
    (output : Output) :
    ((source table output).restriction 0 []).eval 0 +
        ((source table output).restriction 0 []).eval 1 =
      ∑ row : Fin 1024, liftBase (residual pub table
        (outputCoordinate output) row.val) := by
  rw [(source table output).initialBoundary]
  apply Finset.sum_congr rfl
  intro row _
  exact booleanTable_eq_literal_residual pub table output row

#print axioms outputSpec
#print axioms source
#print axioms booleanTable_eq_literal_residual
#print axioms rustPathOutput_eq_sourceValue
#print axioms source_initial_is_literal_residual
end AspisV8Completion.SelectedPathOutputsSourcePolynomial
