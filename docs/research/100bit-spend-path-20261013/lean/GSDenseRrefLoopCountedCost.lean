import CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness
import GSDensePivotScanCost

set_option autoImplicit false

namespace CompPoly.DenseMatrix

/-- A scan-costed execution of the concrete dense RREF data loop. One unit is
charged for each candidate row visited by the actual pivot search. The result
contains the same data/pivot pair as the uninstrumented loop. -/
def rrefLoopDataCounted {F : Type*} [Field F] [BEq F]
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
            let rest := rrefLoopDataCounted fuel rows cols (col + 1) row data pivots
            (rest.1, scan.2 + rest.2)
        | some pivotRow =>
            let data := swapRowsData cols pivotRow row data
            let data := normalizeAndEliminateData rows cols row col data
            let rest := rrefLoopDataCounted fuel rows cols (col + 1) (row + 1)
              data (pivots.push col)
            (rest.1, scan.2 + rest.2)
      else ((data, pivots), 0)

theorem rrefLoopDataCounted_refines {F : Type*} [Field F] [BEq F]
    (fuel rows cols col row : Nat) (data : Array F) (pivots : Array Nat) :
    (rrefLoopDataCounted fuel rows cols col row data pivots).1 =
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
          | none => simp [rrefLoopDataCounted, rrefLoopData, M, hcol, hrow, hscan, hp, ih]
          | some pivotRow => simp [rrefLoopDataCounted, rrefLoopData, M, hcol, hrow, hscan, hp, ih]
        · simp [rrefLoopDataCounted, rrefLoopData, M, hcol, hrow]
      · simp [rrefLoopDataCounted, rrefLoopData, M, hcol]

theorem rrefLoopDataCounted_scan_cost_le {F : Type*} [Field F] [BEq F]
    (fuel rows cols col row : Nat) (data : Array F) (pivots : Array Nat) :
    (rrefLoopDataCounted fuel rows cols col row data pivots).2 ≤ fuel * rows := by
  induction fuel generalizing col row data pivots with
  | zero => simp [rrefLoopDataCounted]
  | succ fuel ih =>
      by_cases hactive : (decide (col < cols) && decide (row < rows)) = true
      · simp only [rrefLoopDataCounted, hactive, if_true]
        have hscan_le :
            (findPivotRowCounted
              ({ rows := rows, cols := cols, data := data } : DenseMatrix F) row col).2 ≤ rows :=
          findPivotRowCounted_steps_le_rows _ row col
        cases hscan : (findPivotRowCounted
            ({ rows := rows, cols := cols, data := data } : DenseMatrix F) row col).1 with
        | none =>
            simp only [hscan]
            have hrec := ih (col + 1) row data pivots
            have hboth := Nat.add_le_add hscan_le hrec
            rw [Nat.succ_mul]
            omega
        | some pivotRow =>
            simp only [hscan]
            have hrec := ih (col + 1) (row + 1)
              (normalizeAndEliminateData rows cols row col
                (swapRowsData cols pivotRow row data)) (pivots.push col)
            have hboth := Nat.add_le_add hscan_le hrec
            rw [Nat.succ_mul]
            omega
      · simp [rrefLoopDataCounted, hactive]

/-- The standard initial fuel is `cols + 1`, so the exact total pivot-scan
iterations are bounded by `(cols + 1) * rows`. -/
theorem rrefLoopDataCounted_initial_scan_cost_le {F : Type*} [Field F] [BEq F]
    (rows cols : Nat) (data : Array F) (pivots : Array Nat) :
    (rrefLoopDataCounted (cols + 1) rows cols 0 0 data pivots).2 ≤
      (cols + 1) * rows :=
  rrefLoopDataCounted_scan_cost_le (cols + 1) rows cols 0 0 data pivots

#print axioms rrefLoopDataCounted_refines
#print axioms rrefLoopDataCounted_scan_cost_le
#print axioms rrefLoopDataCounted_initial_scan_cost_le

end CompPoly.DenseMatrix
