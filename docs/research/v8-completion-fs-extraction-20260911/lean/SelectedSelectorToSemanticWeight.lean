import SelectedSourceTerminalAssembly
import SelectedSelectorExpansion

/-! Connect the selected source's mutable high/low selector expansion to the
row weight consumed by the semantic model.  The imperative expansion theorem
is reused from `SelectedSelectorExpansion`; this leaf closes the remaining
coordinate/index convention, including the six/four split and MSB order.

The Rust-to-field translation of `PreparedQm31Multiplier` remains a separate
low-level arithmetic refinement. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.SelectedSelectorToSemanticWeight
open scoped BigOperators
open AspisV8.SelectedSelectorExpansion
open AspisV8.SelectedSemanticLaneAggregation

variable {K : Type*} [Field K]

/-- Total natural-index view of one ten-coordinate challenge point.  Only the
first ten coordinates are read by the source expansion. -/
def pointNat (point : Fin 10 → K) (index : Nat) : K :=
  if inRange : index < 10 then point ⟨index, inRange⟩ else 0

@[simp] theorem pointNat_inRange (point : Fin 10 → K) (index : Nat)
    (inRange : index < 10) :
    pointNat point index = point ⟨index, inRange⟩ := by
  simp [pointNat, inRange]

/-- `Selectors::at_point(...).row(row)` computes exactly the semantic MLE row
weight, rather than an independently supplied selector table. -/
theorem selectedSelector_eq_mleRowWeight (point : Fin 10 → K)
    (row : Fin 1024) :
    selectedSelector (pointNat point) row.val = mleRowWeight point row := by
  rw [selected_selector_product _ _ row.isLt]
  unfold tensorProduct mleRowWeight bigEndianBit
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro index membership
  have inRange : index < 10 := Finset.mem_range.mp membership
  rw [pointNat_inRange point index inRange]
  simp only [factor]
  split <;> rfl

#print axioms pointNat_inRange
#print axioms selectedSelector_eq_mleRowWeight
end AspisV8Completion.SelectedSelectorToSemanticWeight
