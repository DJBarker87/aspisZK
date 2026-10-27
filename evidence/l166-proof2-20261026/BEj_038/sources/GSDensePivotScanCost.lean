import CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness

set_option autoImplicit false

namespace CompPoly.DenseMatrix

/-- A counted fold uses one unit for each visited list element. -/
theorem foldl_counted_refines {α β : Type*} (xs : List α)
    (f : β → α → β) (init : β) (fuel : Nat) :
    xs.foldl (fun (s : β × Nat) x => (f s.1 x, s.2 + 1)) (init, fuel) =
      (xs.foldl f init, fuel + xs.length) := by
  induction xs generalizing init fuel with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (f init x) (fuel + 1)]
      simp [Nat.add_assoc] <;> omega

/-- Costed version of the actual in-place pivot candidate scan. Its cost is
the number of candidate rows visited; it returns the same pivot as the
production scan. -/
def findPivotRowCounted {F : Type*} [Zero F] [BEq F]
    (M : DenseMatrix F) (start col : Nat) : Option Nat × Nat :=
  let candidates := List.range' start (M.rows - start)
  candidates.foldl
    (fun (s : Option Nat × Nat) row =>
      (findPivotRowStep M col s.1 row, s.2 + 1))
    (none, 0)

/-- The counted scan refines the existing pivot scan exactly, with one step
for every row in the production loop's `range' start (rows-start)`. -/
theorem findPivotRowCounted_refines {F : Type*} [Zero F] [BEq F]
    (M : DenseMatrix F) (start col : Nat) :
    findPivotRowCounted M start col =
      (findPivotRow M start col, M.rows - start) := by
  unfold findPivotRowCounted
  rw [foldl_counted_refines]
  rw [findPivotRow_eq_fold]
  simp [List.length_range']

/-- Each pivot search in the dense kernel scans at most the matrix row count.
This counts row-candidate iterations, not field arithmetic or array-copy cost. -/
theorem findPivotRowCounted_steps_le_rows {F : Type*} [Zero F] [BEq F]
    (M : DenseMatrix F) (start col : Nat) :
    (findPivotRowCounted M start col).2 ≤ M.rows := by
  rw [findPivotRowCounted_refines]
  exact Nat.sub_le _ _

/-- The in-place backend's pivot scan has the same row-iteration count and
selected pivot as the counted refinement. -/
theorem findPivotRowData_counted_refines {F : Type*} [Zero F] [BEq F]
    (M : DenseMatrix F) (start col : Nat) :
    findPivotRowCounted M start col =
      (findPivotRowData M.rows M.cols start col M.data, M.rows - start) := by
  rw [findPivotRowCounted_refines, findPivotRowData_eq]

#print axioms findPivotRowCounted_refines
#print axioms findPivotRowCounted_steps_le_rows
#print axioms findPivotRowData_counted_refines

end CompPoly.DenseMatrix
