import SelectedAbsorptionOutputsSourcePolynomial

/-! Chronological source polynomials for all sixteen selected initial outputs.

The selected callback adds the initial schedule and the twelve transfer
occupancy residuals into positions 0..11.  This file preserves that addition;
positions 12..15 contain only the schedule residual. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

namespace AspisV8Completion.SelectedInitialOutputsSourcePolynomial
open Polynomial
open AspisFormal.HashMerkleModel
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

def indicatorTable (predicate : Nat → Prop) [DecidablePred predicate] :
    Fin 1024 → K := fun row => if predicate row.val then 1 else 0

def mleValue (table : Fin 1024 → K) (point : Fin 10 → K) : K :=
  tableMLEValue point table

noncomputable def mleSlice (table : Fin 1024 → K) (fixed : Fin 10 → K)
    (round : Fin 10) : K[X] := openingSlice table fixed round

theorem mleSlice_degree (table : Fin 1024 → K) (fixed : Fin 10 → K)
    (round : Fin 10) : (mleSlice table fixed round).natDegree ≤ 1 :=
  openingSlice_degree table fixed round

theorem mleSlice_eval_at (table : Fin 1024 → K) (fixed : Fin 10 → K)
    (round : Fin 10) (x : K) :
    (mleSlice table fixed round).eval x =
      mleValue table (replaceCoordinate fixed round x) :=
  openingSlice_eval_at table fixed round x

def fullInitial (row : Nat) : Prop := row % 16 = 0 ∧ firstBlock (row / 16)
def rateInitial (column : Fin 16) (row : Nat) : Prop :=
  row % 16 = 0 ∧ nodeBlock (row / 16) ∧ column.val < 8
instance : DecidablePred fullInitial := fun _ => by unfold fullInitial; infer_instance
instance (column : Fin 16) : DecidablePred (rateInitial column) :=
  fun _ => by unfold rateInitial; infer_instance

def fullTable : Fin 1024 → K := indicatorTable fullInitial
def rateTable (column : Fin 16) : Fin 1024 → K := indicatorTable (rateInitial column)
def targetTable (column : Fin 16) : Fin 1024 → K := fun row =>
  if fullInitial row.val then
    liftBase (initState (firstDomain (row.val / 16))
      (firstLength (row.val / 16)) column)
  else 0
def inputTable : Fin 1024 → K := indicatorTable (fun row => row = 1017)
def outputTable : Fin 1024 → K := indicatorTable (fun row => row = 1018)

def openValue (table : BaseTable) (point : Fin 10 → K) (column : Nat) : K :=
  tableMLEValue point (traceTable table 0 column)
noncomputable def openSlice (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (column : Nat) : K[X] :=
  openingSlice (traceTable table 0 column) fixed round

theorem openSlice_eval_at (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (column : Nat) (x : K) :
    (openSlice table fixed round column).eval x =
      openValue table (replaceCoordinate fixed round x) column :=
  openingSlice_eval_at (traceTable table 0 column) fixed round x

def scheduleValue (table : BaseTable) (point : Fin 10 → K)
    (column : Fin 16) : K :=
  mleValue fullTable point * openValue table point column.val +
    mleValue (rateTable column) point * openValue table point column.val -
      mleValue (targetTable column) point

noncomputable def scheduleSlice (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (column : Fin 16) : K[X] :=
  mleSlice fullTable fixed round * openSlice table fixed round column.val +
    mleSlice (rateTable column) fixed round * openSlice table fixed round column.val -
      mleSlice (targetTable column) fixed round

def occupancyValue (table : BaseTable) (point : Fin 10 → K)
    (column : Fin 16) : K :=
  let input := mleValue inputTable point
  let output := mleValue outputTable point
  let both := input + output
  let z := fun index => openValue table point index
  if column.val = 0 then both * (z 0 * (z 0 - 1))
  else if column.val = 1 then both * (z 9 * z 1 - z 0)
  else if column.val = 2 then both * ((1 - z 0) * z 1)
  else if column.val < 11 then both * ((1 - z 0) * z (column.val - 1))
  else if column.val = 11 then
    input * (z 10 * (1 - z 0)) + output * (z 0 - 1)
  else 0

noncomputable def occupancySlice (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (column : Fin 16) : K[X] :=
  let input := mleSlice inputTable fixed round
  let output := mleSlice outputTable fixed round
  let both := input + output
  let z := fun index => openSlice table fixed round index
  if column.val = 0 then both * (z 0 * (z 0 - 1))
  else if column.val = 1 then both * (z 9 * z 1 - z 0)
  else if column.val = 2 then both * ((1 - z 0) * z 1)
  else if column.val < 11 then both * ((1 - z 0) * z (column.val - 1))
  else if column.val = 11 then
    input * (z 10 * (1 - z 0)) + output * (z 0 - 1)
  else 0

theorem degree_add_one {a b : K[X]} (ha : a.natDegree ≤ 1)
    (hb : b.natDegree ≤ 1) : (a + b).natDegree ≤ 1 :=
  (natDegree_add_le _ _).trans (max_le ha hb)

theorem degree_sub_one {a b : K[X]} (ha : a.natDegree ≤ 1)
    (hb : b.natDegree ≤ 1) : (a - b).natDegree ≤ 1 :=
  (natDegree_sub_le _ _).trans (max_le ha hb)

theorem degree_mul_two {a b : K[X]} (ha : a.natDegree ≤ 1)
    (hb : b.natDegree ≤ 1) : (a * b).natDegree ≤ 2 :=
  natDegree_mul_le.trans ((Nat.add_le_add ha hb).trans (by omega))

theorem degree_mul_three {a b : K[X]} (ha : a.natDegree ≤ 1)
    (hb : b.natDegree ≤ 2) : (a * b).natDegree ≤ 3 :=
  natDegree_mul_le.trans ((Nat.add_le_add ha hb).trans (by omega))

theorem scheduleSlice_degree (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (column : Fin 16) :
    (scheduleSlice table fixed round column).natDegree ≤ 2 := by
  unfold scheduleSlice
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le <;> exact degree_mul_two (mleSlice_degree _ _ _)
      (openingSlice_degree _ _ _)
  · exact (mleSlice_degree _ _ _).trans (by omega)

theorem occupancySlice_degree (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (column : Fin 16) :
    (occupancySlice table fixed round column).natDegree ≤ 3 := by
  unfold occupancySlice
  have input : (mleSlice inputTable fixed round).natDegree ≤ 1 := mleSlice_degree _ _ _
  have output : (mleSlice outputTable fixed round).natDegree ≤ 1 := mleSlice_degree _ _ _
  have both := degree_add_one input output
  have z (index : Nat) : (openSlice table fixed round index).natDegree ≤ 1 :=
    openingSlice_degree _ _ _
  split <;> rename_i condition
  · exact degree_mul_three both (degree_mul_two (z 0)
      (degree_sub_one (z 0) (by simp)))
  split <;> rename_i condition
  · exact degree_mul_three both ((natDegree_sub_le _ _).trans
      (max_le (degree_mul_two (z 9) (z 1)) ((z 0).trans (by omega))))
  split <;> rename_i condition
  · exact degree_mul_three both (degree_mul_two
      (degree_sub_one (by simp) (z 0)) (z 1))
  split <;> rename_i condition
  · exact degree_mul_three both (degree_mul_two
      (degree_sub_one (by simp) (z 0)) (z (column.val - 1)))
  split <;> rename_i condition
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · exact degree_mul_three input (degree_mul_two (z 10)
        (degree_sub_one (by simp) (z 0)))
    · exact (degree_mul_two output (degree_sub_one (z 0) (by simp))).trans
        (by omega)
  · simp

set_option maxRecDepth 10000 in
theorem scheduleSlice_eval_at (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (column : Fin 16) (x : K) :
    (scheduleSlice table fixed round column).eval x =
      scheduleValue table (replaceCoordinate fixed round x) column := by
  change (mleSlice fullTable fixed round * openSlice table fixed round column.val +
      mleSlice (rateTable column) fixed round * openSlice table fixed round column.val -
        mleSlice (targetTable column) fixed round).eval x = _
  rw [eval_sub, eval_add, eval_mul, eval_mul, mleSlice_eval_at,
    mleSlice_eval_at, mleSlice_eval_at, openSlice_eval_at]
  rfl

theorem occupancySlice_eval_at (table : BaseTable) (fixed : Fin 10 → K)
    (round : Fin 10) (column : Fin 16) (x : K) :
    (occupancySlice table fixed round column).eval x =
      occupancyValue table (replaceCoordinate fixed round x) column := by
  unfold occupancySlice occupancyValue
  split_ifs <;> simp only [eval_mul, eval_sub, eval_add, eval_one,
    mleSlice_eval_at, openSlice_eval_at, eval_zero]

noncomputable def outputSpec (table : BaseTable) (column : Fin 16) :
    CoordinateSlices (K := K) where
  value := fun point => scheduleValue table point column + occupancyValue table point column
  slice := fun fixed round => scheduleSlice table fixed round column +
    occupancySlice table fixed round column
  degree := by
    intro fixed round
    exact (natDegree_add_le _ _).trans (max_le
      ((scheduleSlice_degree table fixed round column).trans (by omega))
      ((occupancySlice_degree table fixed round column).trans (by omega)))
  eval_at := by
    intro fixed round x
    rw [eval_add, scheduleSlice_eval_at, occupancySlice_eval_at]

noncomputable def source (table : BaseTable) (column : Fin 16) :
    SourcePolynomial (booleanTable (outputSpec table column)) :=
  BooleanSuffixSourceConstructor.source (outputSpec table column)

theorem indicator_boolean (predicate : Nat → Prop) [DecidablePred predicate]
    (row : Fin 1024) :
    mleValue (indicatorTable predicate) (booleanTracePoint row) =
      if predicate row.val then 1 else 0 :=
  tableMLEValue_booleanTracePoint _ _

theorem table_boolean (table : Fin 1024 → K) (row : Fin 1024) :
    mleValue table (booleanTracePoint row) = table row :=
  tableMLEValue_booleanTracePoint _ _

theorem fullTable_boolean (row : Fin 1024) :
    mleValue fullTable (booleanTracePoint row) =
      if fullInitial row.val then 1 else 0 :=
  indicator_boolean fullInitial row

theorem rateTable_boolean (column : Fin 16) (row : Fin 1024) :
    mleValue (rateTable column) (booleanTracePoint row) =
      if rateInitial column row.val then 1 else 0 :=
  indicator_boolean (rateInitial column) row

theorem inputTable_boolean (row : Fin 1024) :
    mleValue inputTable (booleanTracePoint row) =
      if row.val = 1017 then 1 else 0 :=
  indicator_boolean (fun value => value = 1017) row

theorem outputTable_boolean (row : Fin 1024) :
    mleValue outputTable (booleanTracePoint row) =
      if row.val = 1018 then 1 else 0 :=
  indicator_boolean (fun value => value = 1018) row

theorem openValue_boolean (table : BaseTable) (column : Nat) (row : Fin 1024) :
    openValue table (booleanTracePoint row) column = liftBase (table row.val column) := by
  exact traceTable_boolean table 0 column row

theorem scheduleValue_boolean (table : BaseTable) (column : Fin 16)
    (row : Fin 1024) :
    scheduleValue table (booleanTracePoint row) column =
      liftBase (initialResidual table row.val column) := by
  unfold scheduleValue initialResidual gate
  rw [fullTable_boolean, rateTable_boolean, table_boolean, openValue_boolean]
  by_cases full : row.val % 16 = 0 ∧ firstBlock (row.val / 16)
  · by_cases rate : row.val % 16 = 0 ∧ nodeBlock (row.val / 16) ∧ column.val < 8
    · simp [full, rate, targetTable, fullInitial, rateInitial,
        liftBase_add, liftBase_sub]
      ring
    · have notRate : ¬(nodeBlock (row.val / 16) ∧ column.val < 8) := by
        intro candidate
        exact rate ⟨full.1, candidate⟩
      simp [full, rate, notRate, targetTable, fullInitial, rateInitial,
        liftBase_add, liftBase_sub]
  · by_cases rate : row.val % 16 = 0 ∧ nodeBlock (row.val / 16) ∧ column.val < 8
    · have notFull : ¬ firstBlock (row.val / 16) := by
        intro candidate
        exact full ⟨rate.1, candidate⟩
      simp [full, rate, notFull, targetTable, fullInitial, rateInitial,
        liftBase_add, liftBase_zero]
    · by_cases rowZero : row.val % 16 = 0
      · have notFirst : ¬ firstBlock (row.val / 16) := by
          intro candidate
          exact full ⟨rowZero, candidate⟩
        have notRate : ¬(nodeBlock (row.val / 16) ∧ column.val < 8) := by
          intro candidate
          exact rate ⟨rowZero, candidate⟩
        simp [full, rate, rowZero, notFirst, notRate, targetTable,
          fullInitial, rateInitial, liftBase_zero]
      · simp [full, rate, rowZero, targetTable, fullInitial, rateInitial,
          liftBase_zero]

theorem occupancyValue_boolean (table : BaseTable) (column : Fin 16)
    (row : Fin 1024) :
    occupancyValue table (booleanTracePoint row) column =
      liftBase (occupancyResidual table row.val column.val) := by
  unfold occupancyValue occupancyResidual gate
  rw [inputTable_boolean, outputTable_boolean]
  simp only [openValue_boolean]
  split <;> rename_i h0
  · by_cases input : row.val = 1017 <;> by_cases output : row.val = 1018 <;>
      simp [input, output, liftBase_mul, liftBase_sub, liftBase_one, liftBase_zero]
  split <;> rename_i h1
  · by_cases input : row.val = 1017 <;> by_cases output : row.val = 1018 <;>
      simp [input, output, liftBase_mul, liftBase_sub, liftBase_zero]
  split <;> rename_i h2
  · by_cases input : row.val = 1017 <;> by_cases output : row.val = 1018 <;>
      simp [input, output, liftBase_mul, liftBase_sub, liftBase_one, liftBase_zero]
  split <;> rename_i hlt
  · by_cases input : row.val = 1017 <;> by_cases output : row.val = 1018 <;>
      simp [input, output, liftBase_mul, liftBase_sub, liftBase_one, liftBase_zero]
  split <;> rename_i h11
  · by_cases input : row.val = 1017 <;> by_cases output : row.val = 1018 <;>
      simp [input, output, liftBase_mul, liftBase_sub, liftBase_add, liftBase_one,
        liftBase_zero]
  · simp [h0, h1, h2, hlt, h11, liftBase_zero]

theorem booleanTable_eq_literal_residual (pub : Public) (table : BaseTable)
    (column : Fin 16) (row : Fin 1024) :
    booleanTable (outputSpec table column) row =
      liftBase (residual pub table (.initial column) row.val) := by
  change scheduleValue table (booleanTracePoint row) column +
      occupancyValue table (booleanTracePoint row) column =
        liftBase (initialResidual table row.val column +
          occupancyResidual table row.val column.val)
  rw [scheduleValue_boolean, occupancyValue_boolean, liftBase_add]

/-- Array-level selected initial coordinate after schedule and occupancy are
added into the same packed source position. -/
def rustInitialOutput (table : BaseTable) (point : Fin 10 → K)
    (z : RustArray) (column : Fin 16) : K :=
  scheduleValue table point column +
    (let input := mleValue inputTable point
     let output := mleValue outputTable point
     let both := input + output
     if column.val = 0 then both * (z 0 * (z 0 - 1))
     else if column.val = 1 then both * (z 9 * z 1 - z 0)
     else if column.val = 2 then both * ((1 - z 0) * z 1)
     else if column.val < 11 then both * ((1 - z 0) * z ⟨column.val - 1, by omega⟩)
     else if column.val = 11 then
       input * (z 10 * (1 - z 0)) + output * (z 0 - 1)
     else 0)

theorem outputSpec_value (table : BaseTable) (point : Fin 10 → K)
    (column : Fin 16) :
    (outputSpec table column).value point =
      scheduleValue table point column + occupancyValue table point column := by
  rfl

theorem openingArray_at (table : BaseTable) (point : Fin 10 → K)
    (column : Fin 16) :
    openingArray table point 0 column = openValue table point column.val := by
  rfl

theorem rustInitialOutput_eq_sourceValue (table : BaseTable) (point : Fin 10 → K)
    (column : Fin 16) :
    rustInitialOutput table point (openingArray table point 0) column =
      (outputSpec table column).value point := by
  rw [outputSpec_value]
  unfold rustInitialOutput occupancyValue
  split_ifs <;> simp only [openingArray_at, Fin.val_zero] <;> norm_num

theorem source_initial_is_literal_residual (pub : Public) (table : BaseTable)
    (column : Fin 16) :
    ((source table column).restriction 0 []).eval 0 +
        ((source table column).restriction 0 []).eval 1 =
      ∑ row : Fin 1024, liftBase (residual pub table (.initial column) row.val) := by
  rw [(source table column).initialBoundary]
  apply Finset.sum_congr rfl
  intro row _
  exact booleanTable_eq_literal_residual pub table column row

#print axioms outputSpec
#print axioms source
#print axioms booleanTable_eq_literal_residual
#print axioms rustInitialOutput_eq_sourceValue
#print axioms source_initial_is_literal_residual
end AspisV8Completion.SelectedInitialOutputsSourcePolynomial
