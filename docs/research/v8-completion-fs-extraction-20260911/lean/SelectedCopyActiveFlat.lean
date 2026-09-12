import SelectedSelectorToSemanticWeight
import SelectedWeightedCopyRows

/-! Field-level flattened specification of the selected Copy active mask.

The mask is the literal 64-word `ACTIVE_ROW_MASKS` table already frozen in
`SelectedWeightedCopyRows`.  The selector for every active row is obtained
from the proved source expansion, not supplied independently.  This closes
the mathematical active-functional identity; regrouping it through Rust's
`selector_mask_sum_16` complement optimisation remains a small source-loop
refinement. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.SelectedCopyActiveFlat
open scoped BigOperators
open AspisV8Completion.SelectedSelectorToSemanticWeight
open AspisV8.SelectedSelectorExpansion
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedWeightedCopyRows

variable {K : Type*} [Field K] [DecidableEq K]

def activeIndicator (row : Fin 1024) : K :=
  if rowActive row then 1 else 0

/-- Expansion of the literal source mask into its active row selectors. -/
def sourceActiveFlat (point : Fin 10 → K) : K :=
  ∑ row : Fin 1024,
    selectedSelector (pointNat point) row.val * activeIndicator row

/-- The actual selected selector expansion makes the flattened source mask
exactly the MLE of the public active-row indicator. -/
theorem sourceActiveFlat_eq_tableMLEValue (point : Fin 10 → K) :
    sourceActiveFlat point = tableMLEValue point activeIndicator := by
  unfold sourceActiveFlat tableMLEValue
  apply Finset.sum_congr rfl
  intro row _
  rw [selectedSelector_eq_mleRowWeight]

/-- At a Boolean trace row, the active functional is the literal source mask
bit for that row. -/
theorem sourceActiveFlat_boolean (selected : Fin 1024) :
    sourceActiveFlat (booleanTracePoint selected : Fin 10 → K) =
      activeIndicator selected := by
  rw [sourceActiveFlat_eq_tableMLEValue,
    tableMLEValue_booleanTracePoint]

#print axioms sourceActiveFlat_eq_tableMLEValue
#print axioms sourceActiveFlat_boolean
end AspisV8Completion.SelectedCopyActiveFlat
