import SelectedRangeOutputsSourcePolynomial

/-! Chronological source polynomials for five selected value/amount outputs.

This covers auxiliary-next, auxiliary-XOR12, both conservation equations,
and the positive-transfer product.  Every object is built from exact selector
and committed-table opening slices; Boolean-table correspondence is proved
against the literal selected residual.  Recomposition remains separate
because its reverse-Horner producer equality is a distinct source seam. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 2500

namespace AspisV8Completion.SelectedValueAuxiliarySourcePolynomial
open Polynomial
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.BooleanSuffixSourceConstructor
open AspisV8Completion.BooleanSuffixSourceAlgebra
open AspisV8Completion.SelectedRangeOutputsSourcePolynomial

abbrev K := QM31Exact

def traceTable (table : BaseTable) (view : Fin 3) (column : Nat) :
    Fin 1024 → K := fun row => liftBase (table (viewRow row.val view) column)

def selected1014 : Fin 1024 := ⟨1014, by decide⟩

noncomputable def auxiliarySpec (table : BaseTable) (view : Fin 3) :
    CoordinateSlices (K := K) where
  value := fun point => rangeSelectorValue point *
    tableMLEValue point (traceTable table view 10)
  slice := fun fixed round => rangeSelectorSlice fixed round *
    openingSlice (traceTable table view 10) fixed round
  degree := by
    intro fixed round
    exact natDegree_mul_le.trans ((Nat.add_le_add
      (rangeSelectorSlice_degree fixed round)
      (openingSlice_degree (traceTable table view 10) fixed round)).trans (by omega))
  eval_at := by
    intro fixed round x
    simp only [eval_mul, rangeSelectorSlice_eval_at, openingSlice_eval_at]

noncomputable def auxiliaryNextSpec (table : BaseTable) : CoordinateSlices (K := K) :=
  auxiliarySpec table 1

noncomputable def auxiliaryXorSpec (table : BaseTable) : CoordinateSlices (K := K) :=
  auxiliarySpec table 2

noncomputable def conservationSpec (table : BaseTable) (which : Fin 2) :
    CoordinateSlices (K := K) where
  value := fun point => mleRowWeight point selected1014 *
    if which.val = 0 then
      tableMLEValue point (traceTable table 0 0) -
        tableMLEValue point (traceTable table 0 1) -
        tableMLEValue point (traceTable table 0 2)
    else tableMLEValue point (traceTable table 1 0) -
      tableMLEValue point (traceTable table 1 1)
  slice := fun fixed round => rowSlice fixed round selected1014 *
    if which.val = 0 then
      openingSlice (traceTable table 0 0) fixed round -
        openingSlice (traceTable table 0 1) fixed round -
        openingSlice (traceTable table 0 2) fixed round
    else openingSlice (traceTable table 1 0) fixed round -
      openingSlice (traceTable table 1 1) fixed round
  degree := by
    intro fixed round
    have selector := rowSlice_degree fixed round selected1014
    have opening (view : Fin 3) (column : Nat) :=
      openingSlice_degree (traceTable table view column) fixed round
    apply natDegree_mul_le.trans
    split
    · have body := (natDegree_sub_le _ _).trans (max_le
        ((natDegree_sub_le _ _).trans (max_le (opening 0 0) (opening 0 1)))
        (opening 0 2))
      exact (Nat.add_le_add selector body).trans (by omega)
    · have body := (natDegree_sub_le _ _).trans
        (max_le (opening 1 0) (opening 1 1))
      exact (Nat.add_le_add selector body).trans (by omega)
  eval_at := by
    intro fixed round x
    rw [eval_mul, rowSlice_eval_at]
    split <;> simp only [eval_sub, openingSlice_eval_at]

noncomputable def conservation0Spec (table : BaseTable) : CoordinateSlices (K := K) :=
  conservationSpec table 0

noncomputable def conservation1Spec (table : BaseTable) : CoordinateSlices (K := K) :=
  conservationSpec table 1

noncomputable def positiveSpec (table : BaseTable) : CoordinateSlices (K := K) where
  value := fun point => mleRowWeight point selected1014 *
    (tableMLEValue point (traceTable table 0 1) *
      tableMLEValue point (traceTable table 1 1) *
      tableMLEValue point (traceTable table 0 3) - 1)
  slice := fun fixed round => rowSlice fixed round selected1014 *
    (openingSlice (traceTable table 0 1) fixed round *
      openingSlice (traceTable table 1 1) fixed round *
      openingSlice (traceTable table 0 3) fixed round - 1)
  degree := by
    intro fixed round
    have selector := rowSlice_degree fixed round selected1014
    have z1 := openingSlice_degree (traceTable table 0 1) fixed round
    have next1 := openingSlice_degree (traceTable table 1 1) fixed round
    have z3 := openingSlice_degree (traceTable table 0 3) fixed round
    calc
      _ ≤ (rowSlice fixed round selected1014).natDegree +
          (openingSlice (traceTable table 0 1) fixed round *
            openingSlice (traceTable table 1 1) fixed round *
            openingSlice (traceTable table 0 3) fixed round - 1).natDegree :=
        natDegree_mul_le
      _ ≤ 1 + 3 := by
        apply Nat.add_le_add selector
        apply (natDegree_sub_le _ _).trans
        apply max_le
        · calc
            _ ≤ (openingSlice (traceTable table 0 1) fixed round *
                openingSlice (traceTable table 1 1) fixed round).natDegree +
                (openingSlice (traceTable table 0 3) fixed round).natDegree :=
              natDegree_mul_le
            _ ≤ (1 + 1) + 1 := Nat.add_le_add
              (natDegree_mul_le.trans (Nat.add_le_add z1 next1)) z3
            _ = 3 := rfl
        · simp
      _ ≤ 27 := by omega
  eval_at := by
    intro fixed round x
    simp only [eval_mul, eval_sub, eval_one, rowSlice_eval_at,
      openingSlice_eval_at]

inductive Output where
  | auxiliaryNext | auxiliaryXor | conservation0 | conservation1 | positive
  deriving DecidableEq, Fintype

noncomputable def outputSpec (table : BaseTable) : Output → CoordinateSlices (K := K)
  | .auxiliaryNext => auxiliaryNextSpec table
  | .auxiliaryXor => auxiliaryXorSpec table
  | .conservation0 => conservation0Spec table
  | .conservation1 => conservation1Spec table
  | .positive => positiveSpec table

def outputCoordinate : Output → Coordinate
  | .auxiliaryNext => .auxiliaryNext
  | .auxiliaryXor => .auxiliaryXor
  | .conservation0 => .conservation 0
  | .conservation1 => .conservation 1
  | .positive => .positive

noncomputable def source (table : BaseTable) (output : Output) :
    SourcePolynomial (booleanTable (outputSpec table output)) :=
  BooleanSuffixSourceConstructor.source (outputSpec table output)

theorem row1014_boolean (row : Fin 1024) :
    mleRowWeight (K := K) (booleanTracePoint row) selected1014 =
      if row.val = 1014 then 1 else 0 := by
  rw [mleRowWeight_booleanTracePoint]
  congr 1
  simp [selected1014, Fin.ext_iff, eq_comm]

theorem traceTable_boolean (table : BaseTable) (view : Fin 3) (column : Nat)
    (row : Fin 1024) :
    tableMLEValue (booleanTracePoint row) (traceTable table view column) =
      liftBase (table (viewRow row.val view) column) :=
  tableMLEValue_booleanTracePoint _ _

theorem booleanTable_eq_literal_residual (pub : Public) (table : BaseTable)
    (output : Output) (row : Fin 1024) :
    booleanTable (outputSpec table output) row =
      liftBase (AspisV8.SelectedSemanticRows.residual pub table
        (outputCoordinate output) row.val) := by
  cases output <;>
    simp only [booleanTable, outputSpec, outputCoordinate]
  · unfold auxiliaryNextSpec auxiliarySpec
    change rangeSelectorValue (booleanTracePoint row) *
      tableMLEValue (booleanTracePoint row) (traceTable table 1 10) = _
    rw [rangeSelectorValue_booleanTracePoint, traceTable_boolean]
    change (if valueMask row.val then 1 else 0) * liftBase (table (row.val + 1) 10) =
      liftBase (if valueMask row.val then table (row.val + 1) 10 else 0)
    by_cases active : valueMask row.val <;> simp [active, liftBase_zero]
  · unfold auxiliaryXorSpec auxiliarySpec
    change rangeSelectorValue (booleanTracePoint row) *
      tableMLEValue (booleanTracePoint row) (traceTable table 2 10) = _
    rw [rangeSelectorValue_booleanTracePoint, traceTable_boolean]
    change (if valueMask row.val then 1 else 0) * liftBase (table (Nat.xor row.val 12) 10) =
      liftBase (if valueMask row.val then table (Nat.xor row.val 12) 10 else 0)
    by_cases active : valueMask row.val <;> simp [active, liftBase_zero]
  · change mleRowWeight (booleanTracePoint row) selected1014 *
      (tableMLEValue (booleanTracePoint row) (traceTable table 0 0) -
        tableMLEValue (booleanTracePoint row) (traceTable table 0 1) -
        tableMLEValue (booleanTracePoint row) (traceTable table 0 2)) = _
    rw [row1014_boolean, traceTable_boolean, traceTable_boolean, traceTable_boolean]
    change (if row.val = 1014 then 1 else 0) *
      (liftBase (table row.val 0) - liftBase (table row.val 1) -
        liftBase (table row.val 2)) =
      liftBase (if row.val = 1014 then
        table row.val 0 - table row.val 1 - table row.val 2 else 0)
    by_cases active : row.val = 1014
    · simp [active, liftBase_sub]
    · simp [active, liftBase_zero]
  · change mleRowWeight (booleanTracePoint row) selected1014 *
      (tableMLEValue (booleanTracePoint row) (traceTable table 1 0) -
        tableMLEValue (booleanTracePoint row) (traceTable table 1 1)) = _
    rw [row1014_boolean, traceTable_boolean, traceTable_boolean]
    change (if row.val = 1014 then 1 else 0) *
      (liftBase (table (row.val + 1) 0) - liftBase (table (row.val + 1) 1)) =
      liftBase (if row.val = 1014 then
        table (row.val + 1) 0 - table (row.val + 1) 1 else 0)
    by_cases active : row.val = 1014
    · simp [active, liftBase_sub]
    · simp [active, liftBase_zero]
  · unfold positiveSpec
    change mleRowWeight (booleanTracePoint row) selected1014 *
      (tableMLEValue (booleanTracePoint row) (traceTable table 0 1) *
        tableMLEValue (booleanTracePoint row) (traceTable table 1 1) *
        tableMLEValue (booleanTracePoint row) (traceTable table 0 3) - 1) = _
    rw [row1014_boolean, traceTable_boolean, traceTable_boolean, traceTable_boolean]
    change (if row.val = 1014 then 1 else 0) *
      (liftBase (table row.val 1) * liftBase (table (row.val + 1) 1) *
        liftBase (table row.val 3) - 1) =
      liftBase (if row.val = 1014 then
        table row.val 1 * table (row.val + 1) 1 * table row.val 3 - 1 else 0)
    by_cases active : row.val = 1014
    · simp [active, liftBase_mul, liftBase_sub, liftBase_one]
    · simp [active, liftBase_zero]

theorem source_initial_is_literal_residual (pub : Public) (table : BaseTable)
    (output : Output) :
    ((source table output).restriction 0 []).eval 0 +
        ((source table output).restriction 0 []).eval 1 =
      ∑ row : Fin 1024, liftBase (AspisV8.SelectedSemanticRows.residual pub table
        (outputCoordinate output) row.val) := by
  rw [(source table output).initialBoundary]
  apply Finset.sum_congr rfl
  intro row _
  exact booleanTable_eq_literal_residual pub table output row

#print axioms auxiliarySpec
#print axioms conservationSpec
#print axioms positiveSpec
#print axioms booleanTable_eq_literal_residual
#print axioms source
#print axioms source_initial_is_literal_residual
end AspisV8Completion.SelectedValueAuxiliarySourcePolynomial
