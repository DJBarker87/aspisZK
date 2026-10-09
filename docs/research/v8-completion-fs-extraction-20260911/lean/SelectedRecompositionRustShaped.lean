import SelectedRecompositionSourcePolynomial

/-! Field-level model of the pinned Rust recomposition producer.

This independently models a sixteen-element opening array, the exact first
ten indices consumed by the reverse iterator/fold, the current/successor/
XOR12 ordering, the two `mul_m31` constants, and the three-row selector sum.
It proves equality to the constructed recomposition source value.  This is
not an Aeneas or machine-semantics translation of Rust. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 2500

namespace AspisV8Completion.SelectedRecompositionRustShaped
open scoped BigOperators
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.BooleanSuffixSourceConstructor
open AspisV8Completion.SelectedRangeOutputsSourcePolynomial
open AspisV8Completion.SelectedValueAuxiliarySourcePolynomial
open AspisV8Completion.SelectedRecompositionSourcePolynomial

abbrev K := QM31Exact
abbrev F := M31Exact
abbrev RustArray := Fin 16 → K

/-- Literal `view[..9].iter().rev().fold(view[9], ...)`, with array reads
represented by the same 0..9 indices of a sixteen-element Rust array. -/
def rustReconstruct10 (view : RustArray) : K :=
  sourceHornerK (fun i => view ⟨i % 16, Nat.mod_lt _ (by decide)⟩) 9
    (view ⟨9, by decide⟩)

theorem rustReconstruct10_eq_sum (view : RustArray) :
    rustReconstruct10 view =
      ∑ bit : Fin 10, view ⟨bit.val, by omega⟩ * (2 : K) ^ bit.val := by
  rw [rustReconstruct10, sourceHornerK_sum]
  have combined :
      (∑ i ∈ Finset.range 9,
        view ⟨i % 16, Nat.mod_lt _ (by decide)⟩ * (2 : K) ^ i) +
          view ⟨9, by decide⟩ * (2 : K) ^ 9 =
        ∑ i ∈ Finset.range 10,
          view ⟨i % 16, Nat.mod_lt _ (by decide)⟩ * (2 : K) ^ i :=
    (Finset.sum_range_succ (fun i =>
      view ⟨i % 16, Nat.mod_lt _ (by decide)⟩ * (2 : K) ^ i) 9).symm
  rw [combined, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro bit _
  have indexEq :
      (⟨bit.val % 16, Nat.mod_lt _ (by decide)⟩ : Fin 16) =
        ⟨bit.val, bit.isLt.trans (by decide)⟩ := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt (bit.isLt.trans (by decide : 10 < 16))
  rw [indexEq]

def firstTen (view : RustArray) : Fin 10 → K :=
  fun bit => view ⟨bit.val, bit.isLt.trans (by decide)⟩

theorem rustReconstruct10_eq_reverseHorner10 (view : RustArray) :
    rustReconstruct10 view = reverseHorner10 (firstTen view) := by
  rw [rustReconstruct10_eq_sum, reverseHorner10_eq_sum]
  rfl

/-- Field-level meaning of the optimised `mul_m31` call. -/
def rustMulM31 (value : K) (scalar : F) : K := value * liftBase scalar

theorem liftBase_1024 : liftBase (1024 : F) = (2 : K) ^ 10 := by
  rw [← liftBase_pow_two]
  congr 1

theorem liftBase_1048576 : liftBase (1048576 : F) = (2 : K) ^ 20 := by
  rw [← liftBase_pow_two]
  congr 1

theorem rustMulM31_1024 (value : K) :
    rustMulM31 value 1024 = value * (2 : K) ^ 10 := by
  rw [rustMulM31, liftBase_1024]

theorem rustMulM31_1048576 (value : K) :
    rustMulM31 value 1048576 = value * (2 : K) ^ 20 := by
  rw [rustMulM31, liftBase_1048576]

/-- The selected evaluator materialises each view as sixteen opening values.
Only indices 0..10 are consumed by recomposition. -/
def openingArray (table : BaseTable) (point : Fin 10 → K) (view : Fin 3) :
    RustArray := fun column => tableMLEValue point (traceTable table view column.val)

theorem firstTen_openingArray (table : BaseTable) (point : Fin 10 → K)
    (view : Fin 3) :
    firstTen (openingArray table point view) = openedView table point view := by
  funext bit
  change tableMLEValue point (traceTable table view bit.val) =
    tableMLEValue point (traceTable table view bit.val)
  rfl

theorem openingArray_ten (table : BaseTable) (point : Fin 10 → K)
    (view : Fin 3) :
    openingArray table point view ⟨10, by decide⟩ =
      tableMLEValue point (traceTable table view 10) := by
  rfl

theorem rustReconstruct10_openingArray (table : BaseTable) (point : Fin 10 → K)
    (view : Fin 3) :
    rustReconstruct10 (openingArray table point view) =
      reverseHorner10 (openedView table point view) := by
  rw [rustReconstruct10_eq_reverseHorner10, firstTen_openingArray]

def rustRangeSelector (selectors : Fin 1024 → K) : K :=
  selectors ⟨1008, by decide⟩ + selectors ⟨1010, by decide⟩ +
    selectors ⟨1012, by decide⟩

theorem rustRangeSelector_mle (point : Fin 10 → K) :
    rustRangeSelector (mleRowWeight point) = rangeSelectorValue point := by
  unfold rustRangeSelector rangeSelectorValue
  simp [Fin.sum_univ_succ, rangeRow]
  ring

/-- The pinned `add_value_lanes` recomposition expression before packing. -/
def rustRecomposition (selectors : Fin 1024 → K)
    (z successor xor12 : RustArray) : K :=
  let reconstructed := rustReconstruct10 z +
    rustMulM31 (rustReconstruct10 successor) 1024 +
    rustMulM31 (rustReconstruct10 xor12) 1048576
  rustRangeSelector selectors * (z ⟨10, by decide⟩ - reconstructed)

theorem rustRecomposition_eq_sourceValue (table : BaseTable)
    (point : Fin 10 → K) :
    rustRecomposition (mleRowWeight point)
        (openingArray table point 0) (openingArray table point 1)
        (openingArray table point 2) =
      (recompositionSpec table).value point := by
  unfold rustRecomposition
  rw [rustRangeSelector_mle,
    rustReconstruct10_openingArray, rustReconstruct10_openingArray,
    rustReconstruct10_openingArray, rustMulM31_1024, rustMulM31_1048576,
    recompositionSpec_value, openingArray_ten]
  unfold literalReconstruction
  ring

#print axioms rustReconstruct10_eq_sum
#print axioms rustReconstruct10_eq_reverseHorner10
#print axioms liftBase_1024
#print axioms liftBase_1048576
#print axioms rustRangeSelector_mle
#print axioms rustRecomposition_eq_sourceValue
end AspisV8Completion.SelectedRecompositionRustShaped
