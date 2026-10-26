import CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness
import GSDenseRowUpdateCountedCost

set_option autoImplicit false

namespace CompPoly.DenseMatrix

/-- Actual outer row-loop step with the data array and counted cell updates. -/
def eliminateRowCounted {F : Type*} [Field F]
    (rows cols pivotRow pivotCol : Nat) (state : Array F × Nat) (row : Nat) :
    Array F × Nat :=
  if row = pivotRow then state else
    let factor := -(state.1.getD (row * cols + pivotCol) 0)
    let update := addScaledRowDataCounted cols row pivotRow factor state.1
    (update.1, state.2 + update.2)

def eliminateRowProduction {F : Type*} [Field F]
    (cols pivotRow pivotCol : Nat) (data : Array F) (row : Nat) : Array F :=
  if (row != pivotRow) = true then
    addScaledRowData cols row pivotRow (-(data.getD (row * cols + pivotCol) 0)) data
  else data

private theorem eliminateRowsProduction_eq_foldl {F : Type*} [Field F]
    (xs : List Nat) (cols pivotRow pivotCol : Nat) (init : Array F) :
    (Id.run (forIn xs init fun row state =>
      if (row != pivotRow) = true then
        pure (ForInStep.yield
          (addScaledRowData cols row pivotRow
            (-(state.getD (row * cols + pivotCol) 0)) state))
      else pure (ForInStep.yield state)) : Array F) =
      xs.foldl (eliminateRowProduction cols pivotRow pivotCol) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons row xs ih =>
      by_cases hrow : row = pivotRow
      · simpa [List.forIn_cons, hrow, eliminateRowProduction] using ih init
      · have hneq : (row != pivotRow) = true := by simp [hrow]
        simpa [List.forIn_cons, hrow, hneq, eliminateRowProduction] using
          ih (addScaledRowData cols row pivotRow
            (-(init.getD (row * cols + pivotCol) 0)) init)

private theorem eliminateRowCounted_fst {F : Type*} [Field F]
    (rows cols pivotRow pivotCol : Nat) (state : Array F × Nat) (row : Nat) :
    (eliminateRowCounted rows cols pivotRow pivotCol state row).1 =
      eliminateRowProduction cols pivotRow pivotCol state.1 row := by
  by_cases h : row = pivotRow
  · simp [eliminateRowCounted, eliminateRowProduction, h]
  · have hneq : (row != pivotRow) = true := by simp [h]
    simp [eliminateRowCounted, eliminateRowProduction, h, hneq,
      addScaledRowDataCounted_refines]

private theorem foldl_counted_fst_refines {α β γ : Type*}
    (xs : List α) (step : β × γ → α → β × γ)
    (prodStep : β → α → β)
    (hstep : ∀ state x, (step state x).1 = prodStep state.1 x)
    (init : β × γ) :
    (xs.foldl step init).1 = xs.foldl prodStep init.1 := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (step init x), hstep]

def normalizeAndEliminateDataCounted {F : Type*} [Field F] [BEq F]
    (rows cols pivotRow pivotCol : Nat) (data : Array F) : Array F × Nat :=
  let pivot := data.getD (pivotRow * cols + pivotCol) 0
  if pivot == 0 then (data, 0) else
    let scaled := scaleRowDataCounted cols pivotRow pivot⁻¹ data
    (List.range' 0 rows).foldl
      (eliminateRowCounted rows cols pivotRow pivotCol) scaled

theorem normalizeAndEliminateDataCounted_refines {F : Type*} [Field F] [BEq F]
    (rows cols pivotRow pivotCol : Nat) (data : Array F) :
    (normalizeAndEliminateDataCounted rows cols pivotRow pivotCol data).1 =
      normalizeAndEliminateData rows cols pivotRow pivotCol data := by
  unfold normalizeAndEliminateDataCounted normalizeAndEliminateData
  by_cases hz : (data.getD (pivotRow * cols + pivotCol) 0 == 0) = true
  · rw [Array.getD_eq_getD_getElem?] at hz ⊢
    simp [hz]
  · rw [Array.getD_eq_getD_getElem?] at hz ⊢
    simp only [hz, Bool.false_eq_true, if_false]
    have hfold := foldl_counted_fst_refines (List.range' 0 rows)
      (eliminateRowCounted rows cols pivotRow pivotCol)
      (eliminateRowProduction cols pivotRow pivotCol)
      (fun state row => eliminateRowCounted_fst rows cols pivotRow pivotCol state row)
      (scaleRowDataCounted cols pivotRow
        ((data[pivotRow * cols + pivotCol]?.getD 0)⁻¹) data)
    rw [hfold]
    rw [scaleRowDataCounted_refines]
    simpa [Std.Legacy.Range.forIn_eq_forIn_range'] using
      (eliminateRowsProduction_eq_foldl (List.range' 0 rows) cols pivotRow pivotCol
        (scaleRowData cols pivotRow ((data[pivotRow * cols + pivotCol]?.getD 0)⁻¹) data)).symm

theorem eliminateRowCounted_cost_step {F : Type*} [Field F]
    (rows cols pivotRow pivotCol : Nat) (state : Array F × Nat) (row : Nat) :
    (eliminateRowCounted rows cols pivotRow pivotCol state row).2 ≤ state.2 + cols := by
  by_cases h : row = pivotRow
  · simp [eliminateRowCounted, h]
  · simp [eliminateRowCounted, h, addScaledRowDataCounted_exact_cost]

theorem eliminateRowsCounted_cost_le {F : Type*} [Field F]
    (rows cols pivotRow pivotCol : Nat) (init : Array F × Nat) :
    ((List.range' 0 rows).foldl
      (eliminateRowCounted rows cols pivotRow pivotCol) init).2 ≤ init.2 + rows * cols := by
  have hgen : ∀ (xs : List Nat) (state : Array F × Nat),
      (xs.foldl (eliminateRowCounted rows cols pivotRow pivotCol) state).2 ≤
        state.2 + xs.length * cols := by
    intro (xs : List Nat)
    induction xs with
    | nil => intro state; simp
    | cons row xs ih =>
        intro state
        simp only [List.foldl_cons]
        have hs := eliminateRowCounted_cost_step rows cols pivotRow pivotCol state row
        have ht := ih (eliminateRowCounted rows cols pivotRow pivotCol state row)
        calc
          _ = (xs.foldl (eliminateRowCounted rows cols pivotRow pivotCol)
                (eliminateRowCounted rows cols pivotRow pivotCol state row)).2 := rfl
          _ ≤ (eliminateRowCounted rows cols pivotRow pivotCol state row).2 + xs.length * cols := ht
          _ ≤ (state.2 + cols) + xs.length * cols := Nat.add_le_add_right hs _
          _ = state.2 + (xs.length + 1) * cols := by
                rw [Nat.add_assoc (state.2) cols (xs.length * cols)]
                rw [Nat.add_comm cols (xs.length * cols)]
                rw [Nat.succ_mul]
  simpa [List.length_range'] using hgen (List.range' 0 rows) init

theorem normalizeAndEliminateDataCounted_cell_cost_le {F : Type*} [Field F] [BEq F]
    (rows cols pivotRow pivotCol : Nat) (data : Array F) :
    (normalizeAndEliminateDataCounted rows cols pivotRow pivotCol data).2 ≤
      (rows + 1) * cols := by
  unfold normalizeAndEliminateDataCounted
  by_cases hz : (data.getD (pivotRow * cols + pivotCol) 0 == 0) = true
  · rw [Array.getD_eq_getD_getElem?] at hz ⊢
    simp [hz]
  · rw [Array.getD_eq_getD_getElem?] at hz ⊢
    simp only [hz, Bool.false_eq_true, if_false]
    have hscale : (scaleRowDataCounted cols pivotRow
        ((data[pivotRow * cols + pivotCol]?.getD 0)⁻¹) data).2 = cols :=
      scaleRowDataCounted_exact_cost cols pivotRow _ data
    have hloop := eliminateRowsCounted_cost_le rows cols pivotRow pivotCol
      (scaleRowDataCounted cols pivotRow ((data[pivotRow * cols + pivotCol]?.getD 0)⁻¹) data)
    have hbound : (scaleRowDataCounted cols pivotRow
        ((data[pivotRow * cols + pivotCol]?.getD 0)⁻¹) data).2 + rows * cols ≤
        (rows + 1) * cols := by
      rw [hscale]
      rw [Nat.add_mul]
      omega
    exact le_trans hloop hbound

#print axioms normalizeAndEliminateDataCounted_refines
#print axioms eliminateRowsCounted_cost_le
#print axioms normalizeAndEliminateDataCounted_cell_cost_le

end CompPoly.DenseMatrix
