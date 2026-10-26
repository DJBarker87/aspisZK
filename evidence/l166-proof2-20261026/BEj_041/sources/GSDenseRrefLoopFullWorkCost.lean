import CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness
import GSDensePivotScanCost
import GSDenseRowUpdateCountedCost
import GSDenseNormalizeCellCount

set_option autoImplicit false

namespace CompPoly.DenseMatrix

/-- Count every candidate row examined by a pivot scan and every column fed to
an actual row-operation loop. The first projection is the production result. -/
def rrefLoopDataFullWorkCounted {F : Type*} [Field F] [BEq F]
    (fuel rows cols col row : Nat) (data : Array F) (pivots : Array Nat) :
    (Array F × Array Nat) × Nat :=
  match fuel with
  | 0 => ((data, pivots), 0)
  | fuel + 1 =>
      if (decide (col < cols) && decide (row < rows)) = true then
        let M : DenseMatrix F := { rows := rows, cols := cols, data := data }
        let scan := findPivotRowCounted M row col
        match scan.1 with
        | none =>
            let rest := rrefLoopDataFullWorkCounted fuel rows cols (col + 1) row data pivots
            (rest.1, scan.2 + rest.2)
        | some pivotRow =>
            let swapped := swapRowsDataCounted cols pivotRow row data
            let normalized := normalizeAndEliminateDataCounted rows cols row col swapped.1
            let rest := rrefLoopDataFullWorkCounted fuel rows cols (col + 1) (row + 1)
              normalized.1 (pivots.push col)
            (rest.1, scan.2 + swapped.2 + normalized.2 + rest.2)
      else ((data, pivots), 0)

theorem rrefLoopDataFullWorkCounted_refines {F : Type*} [Field F] [BEq F]
    (fuel rows cols col row : Nat) (data : Array F) (pivots : Array Nat) :
    (rrefLoopDataFullWorkCounted fuel rows cols col row data pivots).1 =
      rrefLoopData fuel rows cols col row data pivots := by
  induction fuel generalizing col row data pivots with
  | zero => rfl
  | succ fuel ih =>
      let M : DenseMatrix F := { rows := rows, cols := cols, data := data }
      have hscan : (findPivotRowCounted M row col).1 =
          findPivotRowData rows cols row col data := by
        change (findPivotRowCounted M row col).1 =
          findPivotRowData M.rows M.cols row col M.data
        exact congrArg Prod.fst (findPivotRowData_counted_refines M row col)
      by_cases hcol : col < cols
      · by_cases hrow : row < rows
        · cases hp : findPivotRowData rows cols row col data with
          | none =>
              simp [rrefLoopDataFullWorkCounted, rrefLoopData, M,
                hcol, hrow, hscan, hp, ih]
          | some pivotRow =>
              have hswap : (swapRowsDataCounted cols pivotRow row data).1 =
                  swapRowsData cols pivotRow row data :=
                swapRowsDataCounted_refines cols pivotRow row data
              have hnorm := normalizeAndEliminateDataCounted_refines rows cols row col
                (swapRowsDataCounted cols pivotRow row data).1
              rw [hswap] at hnorm
              simp [rrefLoopDataFullWorkCounted, rrefLoopData, M,
                hcol, hrow, hscan, hp, hswap, hnorm, ih]
        · simp [rrefLoopDataFullWorkCounted, rrefLoopData, M, hcol, hrow]
      · simp [rrefLoopDataFullWorkCounted, rrefLoopData, M, hcol]

theorem rrefLoopDataFullWorkCounted_le {F : Type*} [Field F] [BEq F]
    (fuel rows cols col row : Nat) (data : Array F) (pivots : Array Nat) :
    (rrefLoopDataFullWorkCounted fuel rows cols col row data pivots).2 ≤
      fuel * (rows + cols + (rows + 1) * cols) := by
  induction fuel generalizing col row data pivots with
  | zero => simp [rrefLoopDataFullWorkCounted]
  | succ fuel ih =>
      by_cases hactive : (decide (col < cols) && decide (row < rows)) = true
      · simp only [rrefLoopDataFullWorkCounted, hactive, if_true]
        have hscan_le :
            (findPivotRowCounted
              ({ rows := rows, cols := cols, data := data } : DenseMatrix F) row col).2 ≤ rows :=
          findPivotRowCounted_steps_le_rows _ row col
        cases hscan : (findPivotRowCounted
            ({ rows := rows, cols := cols, data := data } : DenseMatrix F) row col).1 with
        | none =>
            simp only [hscan]
            have hrec := ih (col + 1) row data pivots
            have hrows : rows ≤ rows + cols + (rows + 1) * cols := by omega
            calc
              _ = (findPivotRowCounted
                    ({ rows := rows, cols := cols, data := data } : DenseMatrix F) row col).2 +
                    (rrefLoopDataFullWorkCounted fuel rows cols (col + 1) row data pivots).2 := rfl
              _ ≤ rows + fuel * (rows + cols + (rows + 1) * cols) := Nat.add_le_add hscan_le hrec
              _ ≤ (rows + cols + (rows + 1) * cols) +
                    fuel * (rows + cols + (rows + 1) * cols) := Nat.add_le_add_right hrows _
              _ = (fuel + 1) * (rows + cols + (rows + 1) * cols) := by
                    calc
                      _ = fuel * (rows + cols + (rows + 1) * cols) +
                            (rows + cols + (rows + 1) * cols) := Nat.add_comm _ _
                      _ = (fuel + 1) * (rows + cols + (rows + 1) * cols) :=
                            (Nat.succ_mul fuel _).symm
        | some pivotRow =>
            simp only [hscan]
            have hswap := swapRowsDataCounted_exact_cost cols pivotRow row data
            have hnorm := normalizeAndEliminateDataCounted_cell_cost_le rows cols row col
              (swapRowsDataCounted cols pivotRow row data).1
            have hrec := ih (col + 1) (row + 1)
              (normalizeAndEliminateDataCounted rows cols row col
                (swapRowsDataCounted cols pivotRow row data).1).1 (pivots.push col)
            have hswap_le : (swapRowsDataCounted cols pivotRow row data).2 ≤ cols := by
              rw [hswap]
              split_ifs <;> omega
            have hstage :
                (findPivotRowCounted
                    ({ rows := rows, cols := cols, data := data } : DenseMatrix F) row col).2 +
                  (swapRowsDataCounted cols pivotRow row data).2 +
                  (normalizeAndEliminateDataCounted rows cols row col
                    (swapRowsDataCounted cols pivotRow row data).1).2 ≤
                  rows + cols + (rows + 1) * cols := by
              exact Nat.add_le_add (Nat.add_le_add hscan_le hswap_le) hnorm
            calc
              _ = (findPivotRowCounted
                    ({ rows := rows, cols := cols, data := data } : DenseMatrix F) row col).2 +
                    (swapRowsDataCounted cols pivotRow row data).2 +
                    (normalizeAndEliminateDataCounted rows cols row col
                      (swapRowsDataCounted cols pivotRow row data).1).2 +
                    (rrefLoopDataFullWorkCounted fuel rows cols (col + 1) (row + 1)
                      (normalizeAndEliminateDataCounted rows cols row col
                        (swapRowsDataCounted cols pivotRow row data).1).1
                      (pivots.push col)).2 := rfl
              _ ≤ rows + cols + (rows + 1) * cols +
                    fuel * (rows + cols + (rows + 1) * cols) := Nat.add_le_add hstage hrec
              _ = (fuel + 1) * (rows + cols + (rows + 1) * cols) := by
                    calc
                      _ = fuel * (rows + cols + (rows + 1) * cols) +
                            (rows + cols + (rows + 1) * cols) := Nat.add_comm _ _
                      _ = (fuel + 1) * (rows + cols + (rows + 1) * cols) :=
                            (Nat.succ_mul fuel _).symm
      · simp [rrefLoopDataFullWorkCounted, hactive]

/-- Standard `cols + 1` fuel gives a concrete total bound on all row candidates
and row-operation cell iterations. Array-copy and field bit costs are outside
this loop-iteration measure. -/
theorem rrefLoopDataFullWorkCounted_initial_le {F : Type*} [Field F] [BEq F]
    (rows cols : Nat) (data : Array F) (pivots : Array Nat) :
    (rrefLoopDataFullWorkCounted (cols + 1) rows cols 0 0 data pivots).2 ≤
      (cols + 1) * (rows + cols + (rows + 1) * cols) :=
  rrefLoopDataFullWorkCounted_le (cols + 1) rows cols 0 0 data pivots

#print axioms rrefLoopDataFullWorkCounted_refines
#print axioms rrefLoopDataFullWorkCounted_le
#print axioms rrefLoopDataFullWorkCounted_initial_le

end CompPoly.DenseMatrix
