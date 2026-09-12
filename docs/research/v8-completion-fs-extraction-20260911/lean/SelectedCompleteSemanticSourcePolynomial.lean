import SelectedPublicOutputsSourcePolynomial
import SelectedPathOutputsSourcePolynomial
import SelectedRangeOutputsSourcePolynomial
import SelectedRecompositionSourcePolynomial
import SelectedValueAuxiliarySourcePolynomial

/-! Fin-indexed composition of all 95 selected semantic coordinate sources.

This is an exact field-level callback/reference object.  It does not claim
refinement of the pinned mutable packed Rust loop or an Aeneas translation. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 5000

namespace AspisV8Completion.SelectedCompleteSemanticSourcePolynomial
open scoped BigOperators
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSemanticRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.CausalSourcePolynomialTrace
open AspisV8Completion.BooleanSuffixSourceConstructor

abbrev K := QM31Exact

noncomputable def coordinateSpec (pub : Public) (table : BaseTable) :
    Coordinate → CoordinateSlices (K := K)
  | .initial column =>
      SelectedInitialOutputsSourcePolynomial.outputSpec table column
  | .absorption column =>
      SelectedAbsorptionOutputsSourcePolynomial.outputSpec table column
  | .direction =>
      SelectedPathOutputsSourcePolynomial.outputSpec table
        SelectedPathOutputsSourcePolynomial.Output.direction
  | .left limb =>
      SelectedPathOutputsSourcePolynomial.outputSpec table
        (SelectedPathOutputsSourcePolynomial.Output.left limb)
  | .right limb =>
      SelectedPathOutputsSourcePolynomial.outputSpec table
        (SelectedPathOutputsSourcePolynomial.Output.right limb)
  | .rangeBit bit => SelectedRangeOutputsSourcePolynomial.slices table bit
  | .recomposition => SelectedRecompositionSourcePolynomial.recompositionSpec table
  | .auxiliaryNext => SelectedValueAuxiliarySourcePolynomial.outputSpec table
      SelectedValueAuxiliarySourcePolynomial.Output.auxiliaryNext
  | .auxiliaryXor => SelectedValueAuxiliarySourcePolynomial.outputSpec table
      SelectedValueAuxiliarySourcePolynomial.Output.auxiliaryXor
  | .conservation which => SelectedValueAuxiliarySourcePolynomial.outputSpec table
      (if which.val = 0 then
        SelectedValueAuxiliarySourcePolynomial.Output.conservation0
      else SelectedValueAuxiliarySourcePolynomial.Output.conservation1)
  | .digest limb => SelectedPublicOutputsSourcePolynomial.publicOutputSpec pub table
      (SelectedPublicOutputsSourcePolynomial.Output.digest limb)
  | .scalar which => SelectedPublicOutputsSourcePolynomial.publicOutputSpec pub table
      (SelectedPublicOutputsSourcePolynomial.Output.scalar which)
  | .positive => SelectedValueAuxiliarySourcePolynomial.outputSpec table
      SelectedValueAuxiliarySourcePolynomial.Output.positive

def coordinateIndex (coordinate : Coordinate) : Fin 95 :=
  ⟨position coordinate, position_lt coordinate⟩

theorem coordinateIndex_injective : Function.Injective coordinateIndex := by
  intro left right same
  apply position_injective
  exact congrArg Fin.val same

noncomputable def coordinateIndexEquiv : Coordinate ≃ Fin 95 :=
  Equiv.ofBijective coordinateIndex
    ((Fintype.bijective_iff_injective_and_card coordinateIndex).2
      ⟨coordinateIndex_injective, by simp [coordinate_count]⟩)

theorem coordinateIndexEquiv_apply (coordinate : Coordinate) :
    coordinateIndexEquiv coordinate = coordinateIndex coordinate := rfl

theorem coordinateIndexEquiv_position (coordinate : Coordinate) :
    (coordinateIndexEquiv coordinate).val = position coordinate := rfl

noncomputable def indexedSpec (pub : Public) (table : BaseTable) (index : Fin 95) :
    CoordinateSlices (K := K) :=
  coordinateSpec pub table (coordinateIndexEquiv.symm index)

noncomputable def indexedSource (pub : Public) (table : BaseTable)
    (index : Fin 95) : SourcePolynomial (booleanTable (indexedSpec pub table index)) :=
  BooleanSuffixSourceConstructor.source (indexedSpec pub table index)

theorem coordinateSpec_boolean_eq_literal (pub : Public) (table : BaseTable)
    (coordinate : Coordinate) (row : Fin 1024) :
    booleanTable (coordinateSpec pub table coordinate) row =
      liftBase (residual pub table coordinate row.val) := by
  cases coordinate with
  | initial column =>
      exact SelectedInitialOutputsSourcePolynomial.booleanTable_eq_literal_residual
        pub table column row
  | absorption column =>
      exact SelectedAbsorptionOutputsSourcePolynomial.booleanTable_eq_literal_residual
        pub table column row
  | direction =>
      exact SelectedPathOutputsSourcePolynomial.booleanTable_eq_literal_residual pub table
        SelectedPathOutputsSourcePolynomial.Output.direction row
  | left limb =>
      exact SelectedPathOutputsSourcePolynomial.booleanTable_eq_literal_residual pub table
        (SelectedPathOutputsSourcePolynomial.Output.left limb) row
  | right limb =>
      exact SelectedPathOutputsSourcePolynomial.booleanTable_eq_literal_residual pub table
        (SelectedPathOutputsSourcePolynomial.Output.right limb) row
  | rangeBit bit =>
      exact SelectedRangeOutputsSourcePolynomial.booleanTable_eq_rangeBitResidual
        pub table bit row
  | recomposition =>
      exact SelectedRecompositionSourcePolynomial.booleanTable_eq_literal_recomposition
        pub table row
  | auxiliaryNext =>
      exact SelectedValueAuxiliarySourcePolynomial.booleanTable_eq_literal_residual pub table
        SelectedValueAuxiliarySourcePolynomial.Output.auxiliaryNext row
  | auxiliaryXor =>
      exact SelectedValueAuxiliarySourcePolynomial.booleanTable_eq_literal_residual pub table
        SelectedValueAuxiliarySourcePolynomial.Output.auxiliaryXor row
  | conservation which =>
      by_cases zero : which.val = 0
      · have eq0 : which = (0 : Fin 2) := Fin.ext zero
        subst which
        exact SelectedValueAuxiliarySourcePolynomial.booleanTable_eq_literal_residual
          pub table SelectedValueAuxiliarySourcePolynomial.Output.conservation0 row
      · have eq1 : which = (1 : Fin 2) := by
          apply Fin.ext
          omega
        subst which
        exact SelectedValueAuxiliarySourcePolynomial.booleanTable_eq_literal_residual
          pub table SelectedValueAuxiliarySourcePolynomial.Output.conservation1 row
  | digest limb =>
      exact SelectedPublicOutputsSourcePolynomial.booleanTable_eq_literal_residual pub table
        (.digest limb) row
  | scalar which =>
      exact SelectedPublicOutputsSourcePolynomial.booleanTable_eq_literal_residual pub table
        (.scalar which) row
  | positive =>
      exact SelectedValueAuxiliarySourcePolynomial.booleanTable_eq_literal_residual pub table
        SelectedValueAuxiliarySourcePolynomial.Output.positive row

theorem indexedSpec_boolean_eq_literal (pub : Public) (table : BaseTable)
    (index : Fin 95) (row : Fin 1024) :
    booleanTable (indexedSpec pub table index) row =
      liftBase (residual pub table (coordinateIndexEquiv.symm index) row.val) :=
  coordinateSpec_boolean_eq_literal pub table (coordinateIndexEquiv.symm index) row

theorem indexedSource_initial_eq_literal (pub : Public) (table : BaseTable)
    (index : Fin 95) :
    ((indexedSource pub table index).restriction 0 []).eval 0 +
        ((indexedSource pub table index).restriction 0 []).eval 1 =
      ∑ row : Fin 1024,
        liftBase (residual pub table (coordinateIndexEquiv.symm index) row.val) := by
  rw [(indexedSource pub table index).initialBoundary]
  apply Finset.sum_congr rfl
  intro row _
  exact indexedSpec_boolean_eq_literal pub table index row

theorem total_initial_eq_literal (pub : Public) (table : BaseTable) :
    (∑ index : Fin 95,
      (((indexedSource pub table index).restriction 0 []).eval 0 +
        ((indexedSource pub table index).restriction 0 []).eval 1)) =
    ∑ row : Fin 1024, ∑ index : Fin 95,
      liftBase (residual pub table (coordinateIndexEquiv.symm index) row.val) := by
  simp_rw [indexedSource_initial_eq_literal]
  rw [Finset.sum_comm]

#print axioms coordinateIndexEquiv
#print axioms coordinateSpec_boolean_eq_literal
#print axioms indexedSource
#print axioms indexedSource_initial_eq_literal
#print axioms total_initial_eq_literal
end AspisV8Completion.SelectedCompleteSemanticSourcePolynomial
