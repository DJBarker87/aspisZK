import BooleanSuffixSourceAlgebra
import SelectedRangeLaneSourcePolynomial
import SelectedSemanticPackedLiteral

/-! Source-polynomial construction for all thirty selected range-bit outputs.

The Rust `add_value_lanes` path uses one shared selector (rows 1008, 1010,
and 1012) and thirty opened trace values: ten at `z`, ten at `succ_z`, and ten
at `xor12_z`.  Each output is the same degree-three local expression with a
different fixed committed trace-column table.  This leaf constructs every
one of those chronological sources and identifies its Boolean table with the
corresponding selected semantic residual.
It does not claim literal Rust memory/execution refinement or cover the other
65 semantic coordinates. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 2000

namespace AspisV8Completion.SelectedRangeOutputsSourcePolynomial
open Polynomial
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.SelectedRangeLaneCoordinateSlice
open AspisV8Completion.BooleanSuffixSourceConstructor
open AspisV8Completion.BooleanSuffixSourceAlgebra

abbrev K := QM31Exact

/-- The committed Boolean trace table whose MLE is the literal opened value
used by range output `bit`. -/
def rangeOpeningTable (table : BaseTable) (bit : Fin 30) : Fin 1024 → K :=
  fun row => liftBase (bitAt table row.val bit)

noncomputable def slices (table : BaseTable) (bit : Fin 30) :
    CoordinateSlices (K := K) :=
  AspisV8Completion.SelectedRangeLaneSourcePolynomial.slices
    (rangeOpeningTable table bit)

noncomputable def source (table : BaseTable) (bit : Fin 30) :
    SourcePolynomial (booleanTable (slices table bit)) :=
  BooleanSuffixSourceConstructor.source (slices table bit)

theorem rangeSelectorValue_booleanTracePoint (row : Fin 1024) :
    rangeSelectorValue (K := K) (booleanTracePoint row) =
      if valueMask row.val then 1 else 0 := by
  classical
  unfold rangeSelectorValue
  simp only [Fin.sum_univ_succ]
  by_cases at1008 : row.val = 1008
  · have rowEq : row = ⟨1008, by decide⟩ := Fin.ext at1008
    subst row
    simp [rangeRow, mleRowWeight_booleanTracePoint,
      valueMask, Fin.ext_iff]
  by_cases at1010 : row.val = 1010
  · have rowEq : row = ⟨1010, by decide⟩ := Fin.ext at1010
    subst row
    simp [rangeRow, mleRowWeight_booleanTracePoint,
      valueMask, Fin.ext_iff]
  by_cases at1012 : row.val = 1012
  · have rowEq : row = ⟨1012, by decide⟩ := Fin.ext at1012
    subst row
    simp [rangeRow, mleRowWeight_booleanTracePoint,
      valueMask, Fin.ext_iff]
  have not1008 : (1008 : Nat) ≠ row.val := Ne.symm at1008
  have not1010 : (1010 : Nat) ≠ row.val := Ne.symm at1010
  have not1012 : (1012 : Nat) ≠ row.val := Ne.symm at1012
  simp [rangeRow, mleRowWeight_booleanTracePoint,
    valueMask, Fin.ext_iff, at1008, at1010, at1012,
    not1008, not1010, not1012]

theorem rangeOpeningTable_MLE_booleanTracePoint (table : BaseTable)
    (bit : Fin 30) (row : Fin 1024) :
    tableMLEValue (booleanTracePoint row) (rangeOpeningTable table bit) =
      liftBase (bitAt table row.val bit) := by
  exact tableMLEValue_booleanTracePoint _ _

/-- The constructed source's Boolean table is exactly source coordinate
`rangeBit bit`, rather than merely some table with the same MLE. -/
theorem booleanTable_eq_rangeBitResidual (pub : Public) (table : BaseTable)
    (bit : Fin 30) (row : Fin 1024) :
    booleanTable (slices table bit) row =
      liftBase (AspisV8.SelectedSemanticRows.residual pub table (.rangeBit bit) row.val) := by
  unfold booleanTable slices
  change rangeLaneValue (rangeOpeningTable table bit) (booleanTracePoint row) = _
  unfold rangeLaneValue
  rw [rangeSelectorValue_booleanTracePoint,
    rangeOpeningTable_MLE_booleanTracePoint]
  change
    (if valueMask row.val then 1 else 0) *
        (liftBase (bitAt table row.val bit) ^ 2 -
          liftBase (bitAt table row.val bit)) =
      liftBase (if valueMask row.val then
        bitAt table row.val bit ^ 2 - bitAt table row.val bit else 0)
  by_cases active : valueMask row.val
  · simp only [active, if_pos, one_mul]
    rw [liftBase_sub]
    simp only [pow_two]
    rw [liftBase_mul]
  · rw [if_neg active, if_neg active, zero_mul, liftBase_zero]

theorem source_initial_is_literal_range_residual (pub : Public)
    (table : BaseTable) (bit : Fin 30) :
    ((source table bit).restriction 0 []).eval 0 +
        ((source table bit).restriction 0 []).eval 1 =
      ∑ row : Fin 1024,
        liftBase (AspisV8.SelectedSemanticRows.residual pub table (.rangeBit bit) row.val) := by
  rw [(source table bit).initialBoundary]
  apply Finset.sum_congr rfl
  intro row _
  exact booleanTable_eq_rangeBitResidual pub table bit row

theorem source_successor_boundary (table : BaseTable) (bit : Fin 30)
    (previous : Fin 9) (history : List K) (challenge : K)
    (length : history.length = previous.val) :
    ((source table bit).restriction previous.succ (history.concat challenge)).eval 0 +
        ((source table bit).restriction previous.succ (history.concat challenge)).eval 1 =
      ((source table bit).restriction previous.castSucc history).eval challenge :=
  (source table bit).successorBoundary previous history challenge length

/-- Any verifier-fixed linear projection of all thirty range outputs. This is
the form needed by packing and later random linear combination; it is built
from the closure operations rather than reproving ten chronological rounds. -/
noncomputable def weightedSlices (table : BaseTable) (weight : Fin 30 → K) :
    CoordinateSlices (K := K) :=
  finsetSum (fun bit => scale (weight bit) (slices table bit))

noncomputable def weightedSource (table : BaseTable) (weight : Fin 30 → K) :
    SourcePolynomial (booleanTable (weightedSlices table weight)) :=
  BooleanSuffixSourceConstructor.source (weightedSlices table weight)

theorem weightedBooleanTable_eq_literal_range_residuals (pub : Public)
    (table : BaseTable) (weight : Fin 30 → K) (row : Fin 1024) :
    booleanTable (weightedSlices table weight) row =
      ∑ bit : Fin 30, weight bit *
        liftBase (AspisV8.SelectedSemanticRows.residual pub table
          (.rangeBit bit) row.val) := by
  unfold booleanTable weightedSlices
  rw [finsetSum_value]
  apply Finset.sum_congr rfl
  intro bit _
  change weight bit * (slices table bit).value (booleanTracePoint row) = _
  rw [show (slices table bit).value (booleanTracePoint row) =
      booleanTable (slices table bit) row by rfl]
  rw [booleanTable_eq_rangeBitResidual]

theorem weightedSource_initial_is_literal_range_residuals (pub : Public)
    (table : BaseTable) (weight : Fin 30 → K) :
    ((weightedSource table weight).restriction 0 []).eval 0 +
        ((weightedSource table weight).restriction 0 []).eval 1 =
      ∑ row : Fin 1024, ∑ bit : Fin 30, weight bit *
        liftBase (AspisV8.SelectedSemanticRows.residual pub table
          (.rangeBit bit) row.val) := by
  rw [(weightedSource table weight).initialBoundary]
  apply Finset.sum_congr rfl
  intro row _
  exact weightedBooleanTable_eq_literal_range_residuals pub table weight row

#print axioms rangeSelectorValue_booleanTracePoint
#print axioms rangeOpeningTable_MLE_booleanTracePoint
#print axioms booleanTable_eq_rangeBitResidual
#print axioms source
#print axioms source_initial_is_literal_range_residual
#print axioms source_successor_boundary
#print axioms weightedSlices
#print axioms weightedSource
#print axioms weightedBooleanTable_eq_literal_range_residuals
#print axioms weightedSource_initial_is_literal_range_residuals
end AspisV8Completion.SelectedRangeOutputsSourcePolynomial
