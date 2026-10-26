import CompPoly.LinearAlgebra.Dense.KernelInPlaceCorrectness
import GSDensePivotScanCost

set_option autoImplicit false

namespace CompPoly.DenseMatrix

/-- Counted list-fold wrapper: one unit is charged per column element fed to the
actual row-update fold. -/
def countedColumnFold {F : Type*} (cols : Nat) (init : Array F)
    (step : Array F → Nat → Array F) : Array F × Nat :=
  (List.range' 0 cols).foldl
    (fun (state : Array F × Nat) col => (step state.1 col, state.2 + 1))
    (init, 0)

theorem countedColumnFold_refines {F : Type*} (cols : Nat) (init : Array F)
    (step : Array F → Nat → Array F) :
    (countedColumnFold cols init step).1 = (List.range' 0 cols).foldl step init := by
  unfold countedColumnFold
  rw [foldl_counted_refines]

theorem countedColumnFold_count {F : Type*} (cols : Nat) (init : Array F)
    (step : Array F → Nat → Array F) :
    (countedColumnFold cols init step).2 = cols := by
  unfold countedColumnFold
  rw [foldl_counted_refines]
  simp [List.length_range']

/-- Instrumented version of the concrete per-column scale loop. -/
def scaleRowDataCounted {F : Type*} [Field F]
    (cols row : Nat) (factor : F) (data : Array F) : Array F × Nat :=
  countedColumnFold cols data fun state col =>
    let idx := row * cols + col
    setD state idx (factor * state.getD idx 0)

theorem scaleRowDataCounted_refines {F : Type*} [Field F]
    (cols row : Nat) (factor : F) (data : Array F) :
    (scaleRowDataCounted cols row factor data).1 = scaleRowData cols row factor data := by
  unfold scaleRowDataCounted
  rw [countedColumnFold_refines]
  simp [countedColumnFold, countedColumnFold, scaleRowData,
    Std.Legacy.Range.forIn_eq_forIn_range', list_forIn_yield_eq_foldl]

theorem scaleRowDataCounted_exact_cost {F : Type*} [Field F]
    (cols row : Nat) (factor : F) (data : Array F) :
    (scaleRowDataCounted cols row factor data).2 = cols :=
  countedColumnFold_count cols data _

/-- Instrumented version of the concrete per-column swap loop. The equal-row
branch executes no column iterations, matching the production conditional. -/
def swapRowsDataCounted {F : Type*} [Zero F]
    (cols rowA rowB : Nat) (data : Array F) : Array F × Nat :=
  if rowA = rowB then (data, 0) else
    countedColumnFold cols data fun state col =>
      let ia := rowA * cols + col
      let ib := rowB * cols + col
      let a := state.getD ia 0
      let b := state.getD ib 0
      setD (setD state ia b) ib a

theorem swapRowsDataCounted_refines {F : Type*} [Zero F]
    (cols rowA rowB : Nat) (data : Array F) :
    (swapRowsDataCounted cols rowA rowB data).1 = swapRowsData cols rowA rowB data := by
  by_cases h : rowA = rowB
  · simp [swapRowsDataCounted, swapRowsData, h]
  · rw [swapRowsDataCounted, if_neg h, swapRowsData, if_neg h]
    rw [countedColumnFold_refines]
    simp [swapRowsData, h, Std.Legacy.Range.forIn_eq_forIn_range',
      list_forIn_yield_eq_foldl]

theorem swapRowsDataCounted_exact_cost {F : Type*} [Zero F]
    (cols rowA rowB : Nat) (data : Array F) :
    (swapRowsDataCounted cols rowA rowB data).2 = if rowA = rowB then 0 else cols := by
  by_cases h : rowA = rowB <;> simp [swapRowsDataCounted, h, countedColumnFold_count]

/-- Instrumented version of the concrete per-column add-scaled-row loop. -/
def addScaledRowDataCounted {F : Type*} [Field F]
    (cols target source : Nat) (factor : F) (data : Array F) : Array F × Nat :=
  countedColumnFold cols data fun state col =>
    let ti := target * cols + col
    let si := source * cols + col
    setD state ti (state.getD ti 0 + factor * state.getD si 0)

theorem addScaledRowDataCounted_refines {F : Type*} [Field F]
    (cols target source : Nat) (factor : F) (data : Array F) :
    (addScaledRowDataCounted cols target source factor data).1 =
      addScaledRowData cols target source factor data := by
  unfold addScaledRowDataCounted
  rw [countedColumnFold_refines]
  simp [countedColumnFold, countedColumnFold, addScaledRowData,
    Std.Legacy.Range.forIn_eq_forIn_range', list_forIn_yield_eq_foldl]

theorem addScaledRowDataCounted_exact_cost {F : Type*} [Field F]
    (cols target source : Nat) (factor : F) (data : Array F) :
    (addScaledRowDataCounted cols target source factor data).2 = cols :=
  countedColumnFold_count cols data _

#print axioms countedColumnFold_refines
#print axioms countedColumnFold_count
#print axioms scaleRowDataCounted_refines
#print axioms scaleRowDataCounted_exact_cost
#print axioms swapRowsDataCounted_refines
#print axioms swapRowsDataCounted_exact_cost
#print axioms addScaledRowDataCounted_refines
#print axioms addScaledRowDataCounted_exact_cost

end CompPoly.DenseMatrix
