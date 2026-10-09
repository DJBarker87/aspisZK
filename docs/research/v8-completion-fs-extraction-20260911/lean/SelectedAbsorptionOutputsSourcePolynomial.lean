import SelectedPathOutputsSourcePolynomial

/-! Chronological source polynomials for the sixteen absorption outputs.

Each output is the exact literal absorption-row indicator for its lane times
the same-index `z` opening.  This proves the semantic function independently
of the optimised Rust construction of the three shared selector buckets. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 3000

namespace AspisV8Completion.SelectedAbsorptionOutputsSourcePolynomial
open Polynomial
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.BooleanSuffixSourceConstructor
open AspisV8Completion.SelectedValueAuxiliarySourcePolynomial
open AspisV8Completion.SelectedRecompositionRustShaped

abbrev K := QM31Exact

def absorptionActive (column : Fin 16) (row : Nat) : Prop :=
  row % 16 = 12 ∧
    ((2 ≤ column.val ∧ column.val < 8 ∧ chunkTwo (row / 16)) ∨
      (8 ≤ column.val ∧ (chunkTwo (row / 16) ∨ chunkEight (row / 16) ∨
        nodeBlock (row / 16))))

instance (column : Fin 16) : DecidablePred (absorptionActive column) :=
  fun _ => by unfold absorptionActive; infer_instance

def absorptionIndicator (column : Fin 16) : Fin 1024 → K := fun row =>
  if absorptionActive column row.val then 1 else 0

def selectorValue (point : Fin 10 → K) (column : Fin 16) : K :=
  tableMLEValue point (absorptionIndicator column)

noncomputable def selectorSlice (fixed : Fin 10 → K) (round : Fin 10)
    (column : Fin 16) : K[X] :=
  openingSlice (absorptionIndicator column) fixed round

theorem selectorSlice_degree (fixed : Fin 10 → K) (round : Fin 10)
    (column : Fin 16) :
    (selectorSlice fixed round column).natDegree ≤ 1 :=
  openingSlice_degree (absorptionIndicator column) fixed round

theorem selectorSlice_eval_at (fixed : Fin 10 → K) (round : Fin 10)
    (column : Fin 16) (x : K) :
    (selectorSlice fixed round column).eval x =
      selectorValue (replaceCoordinate fixed round x) column :=
  openingSlice_eval_at (absorptionIndicator column) fixed round x

noncomputable def outputSpec (table : BaseTable) (column : Fin 16) :
    CoordinateSlices (K := K) where
  value := fun point => selectorValue point column *
    tableMLEValue point (traceTable table 0 column.val)
  slice := fun fixed round => selectorSlice fixed round column *
    openingSlice (traceTable table 0 column.val) fixed round
  degree := by
    intro fixed round
    exact natDegree_mul_le.trans ((Nat.add_le_add
      (selectorSlice_degree fixed round column)
      (openingSlice_degree (traceTable table 0 column.val) fixed round)).trans
        (by omega))
  eval_at := by
    intro fixed round x
    rw [eval_mul, selectorSlice_eval_at, openingSlice_eval_at]

noncomputable def source (table : BaseTable) (column : Fin 16) :
    SourcePolynomial (booleanTable (outputSpec table column)) :=
  BooleanSuffixSourceConstructor.source (outputSpec table column)

theorem outputSpec_value (table : BaseTable) (column : Fin 16)
    (point : Fin 10 → K) :
    (outputSpec table column).value point = selectorValue point column *
      tableMLEValue point (traceTable table 0 column.val) := by
  rfl

theorem residual_absorption (pub : Public) (table : BaseTable)
    (column : Fin 16) (row : Nat) :
    residual pub table (.absorption column) row = absorptionResidual table row column := by
  rfl

theorem absorptionResidual_eq_active (table : BaseTable) (column : Fin 16)
    (row : Nat) :
    absorptionResidual table row column =
      if absorptionActive column row then table row column.val else 0 := by
  rfl

theorem selectorValue_boolean (column : Fin 16) (row : Fin 1024) :
    selectorValue (booleanTracePoint row) column =
      if absorptionActive column row.val then 1 else 0 := by
  exact tableMLEValue_booleanTracePoint _ _

theorem absorptionActive_eq_source (column : Fin 16) (row : Nat) :
    absorptionActive column row ↔
      (row % 16 = 12 ∧
        ((2 ≤ column.val ∧ column.val < 8 ∧ chunkTwo (row / 16)) ∨
          (8 ≤ column.val ∧ (chunkTwo (row / 16) ∨ chunkEight (row / 16) ∨
            nodeBlock (row / 16))))) := by
  rfl

theorem booleanTable_eq_literal_residual (pub : Public) (table : BaseTable)
    (column : Fin 16) (row : Fin 1024) :
    booleanTable (outputSpec table column) row =
      liftBase (residual pub table (.absorption column) row.val) := by
  change (outputSpec table column).value (booleanTracePoint row) = _
  rw [outputSpec_value, residual_absorption, absorptionResidual_eq_active]
  rw [selectorValue_boolean, traceTable_boolean]
  simp only [viewRow, Fin.val_zero]
  by_cases active : absorptionActive column row.val
  · simp [active]
  · simp [active, liftBase_zero]

/-- Independent array-level execution of the literal final multiply.  The
sixteen selector entries are the semantic functions above.  Equality of the
Rust `fixed/chunk_two/chunk_eight/nodes` bucket construction to those entries
remains a separate finite selector-refinement theorem. -/
def rustAbsorptionOutput (selectors : Fin 16 → K) (z : RustArray)
    (column : Fin 16) : K := selectors column * z column

theorem openingArray_at (table : BaseTable) (point : Fin 10 → K)
    (view : Fin 3) (column : Fin 16) :
    openingArray table point view column =
      tableMLEValue point (traceTable table view column.val) := by
  rfl

theorem rustAbsorptionOutput_eq_sourceValue (table : BaseTable)
    (point : Fin 10 → K) (column : Fin 16) :
    rustAbsorptionOutput (selectorValue point) (openingArray table point 0) column =
      (outputSpec table column).value point := by
  rw [outputSpec_value]
  unfold rustAbsorptionOutput
  rw [openingArray_at]

theorem source_initial_is_literal_residual (pub : Public) (table : BaseTable)
    (column : Fin 16) :
    ((source table column).restriction 0 []).eval 0 +
        ((source table column).restriction 0 []).eval 1 =
      ∑ row : Fin 1024,
        liftBase (residual pub table (.absorption column) row.val) := by
  rw [(source table column).initialBoundary]
  apply Finset.sum_congr rfl
  intro row _
  exact booleanTable_eq_literal_residual pub table column row

#print axioms outputSpec
#print axioms source
#print axioms booleanTable_eq_literal_residual
#print axioms rustAbsorptionOutput_eq_sourceValue
#print axioms source_initial_is_literal_residual
end AspisV8Completion.SelectedAbsorptionOutputsSourcePolynomial
