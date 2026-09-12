import CanonicalTableReferenceTrace

/-! The selected semantic terminal is a degree-27 source polynomial, not the
multilinear extension of its values on the Boolean cube.

`CanonicalTableReferenceTrace` is a correct causal trace for the multilinear
extension of a fixed Boolean table.  It must not be used as the honest trace
of the selected Rust callback without a further polynomial-identity theorem.
The Booleanity polynomial below is the smallest obstruction: it vanishes on
every Boolean row while remaining nonzero at ordinary off-domain points.

The positive result in this file is the exact linear mask identity.  Thus the
Rust expression `mask_value + eta * original` may be refined componentwise,
but its `original` endpoint has to be the actual source-polynomial evaluation,
not `tableMLEValue` of the Boolean restriction.
-/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.SourcePolynomialEndpointObstruction
open scoped BigOperators
open AspisV8.SelectedCompactSemanticRepair
open AspisV8.SelectedSemanticLaneAggregation

variable {K : Type*} [Field K] [DecidableEq K]

/-- Exact linearity needed to split the selected masking terminal. -/
theorem tableMLEValue_maskedTable (eta : K) (real mask : Fin 1024 → K)
    (point : Fin 10 → K) :
    tableMLEValue point (maskedTable eta real mask) =
      tableMLEValue point mask + eta * tableMLEValue point real := by
  classical
  simp only [tableMLEValue, maskedTable, mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply congrArg (tableMLEValue point mask + ·)
  apply Finset.sum_congr rfl
  intro row _
  ring

/-- A literal source-polynomial factor used by Booleanity constraints. -/
def firstCoordinateBooleanity (point : Fin 10 → K) : K :=
  point 0 * (point 0 - 1)

/-- The polynomial has the all-zero Boolean restriction. -/
theorem firstCoordinateBooleanity_booleanRow (row : Fin 1024) :
    firstCoordinateBooleanity (booleanTracePoint (K := K) row) = 0 := by
  unfold firstCoordinateBooleanity
  by_cases bit : bigEndianBit row 0 <;> simp [booleanTracePoint, bit]

def zeroBooleanTable : Fin 1024 → K := fun _ => 0

theorem zeroBooleanTable_mle (point : Fin 10 → K) :
    tableMLEValue point (zeroBooleanTable : Fin 1024 → K) = 0 := by
  classical
  simp [tableMLEValue, zeroBooleanTable]

/-- Equality on every Boolean row does not identify the off-domain source
terminal with the table MLE.  This is the exact missing premise in the old
`callbackReturnsTable` endpoint, rather than a callback implementation fact. -/
theorem booleanRestriction_does_not_fix_sourceEndpoint
    (point : Fin 10 → K)
    (offDomain : firstCoordinateBooleanity point ≠ 0) :
    firstCoordinateBooleanity point ≠
      tableMLEValue point (zeroBooleanTable : Fin 1024 → K) := by
  rw [zeroBooleanTable_mle]
  exact offDomain

#print axioms tableMLEValue_maskedTable
#print axioms firstCoordinateBooleanity_booleanRow
#print axioms zeroBooleanTable_mle
#print axioms booleanRestriction_does_not_fix_sourceEndpoint
end AspisV8Completion.SourcePolynomialEndpointObstruction
