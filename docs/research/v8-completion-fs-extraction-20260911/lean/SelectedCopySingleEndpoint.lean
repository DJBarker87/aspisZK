import SelectedCopyActiveExecutable
import SelectedCopyLayoutRows

/-! One literal `accumulate_endpoint` slice.

For a fixed endpoint and target slot, the Rust update adds the endpoint-row
selector times its compressed value exactly when the slots agree.  This leaf
proves that contribution is the MLE of the Boolean `slotContribution` table.
It does not yet fold all 272 producer/consumer occurrences or identify the
Rust pattern compressor with `SelectedCopyLayoutRows.compressed`. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.SelectedCopySingleEndpoint
open AspisV8.SelectedCopyLayout
open AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedSelectorExpansion
open AspisV8Completion.SelectedSelectorToSemanticWeight

variable {K : Type*} [Field K] [DecidableEq K]

/-- Field contribution made by one call to the source update for one of its
two output slots. -/
def sourceEndpointContribution (point : Fin 10 → K) (endpoint : Endpoint)
    (slot : Fin 2) (value : K) : K :=
  if endpoint.slot = slot then
    selectedSelector (pointNat point) endpoint.row.val * value
  else 0

/-- One endpoint update is exactly evaluation of its row/slot table. -/
theorem sourceEndpointContribution_eq_tableMLEValue
    (point : Fin 10 → K) (endpoint : Endpoint) (slot : Fin 2) (value : K) :
    sourceEndpointContribution point endpoint slot value =
      tableMLEValue point (fun row => slotContribution endpoint row slot value) := by
  classical
  unfold sourceEndpointContribution tableMLEValue
  by_cases sameSlot : endpoint.slot = slot
  · rw [if_pos sameSlot, selectedSelector_eq_mleRowWeight]
    rw [Finset.sum_eq_single endpoint.row]
    · simp [slotContribution, sameSlot]
    · intro row _ different
      have rowDifferent : endpoint.row ≠ row := fun equal => different equal.symm
      simp [slotContribution, rowDifferent]
    · simp
  · rw [if_neg sameSlot]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro row _
    simp [slotContribution, sameSlot]

/-- Boolean specialization: the update contributes only at its exact physical
row and exact compiled slot. -/
theorem sourceEndpointContribution_boolean
    (selected : Fin 1024) (endpoint : Endpoint) (slot : Fin 2) (value : K) :
    sourceEndpointContribution (booleanTracePoint selected) endpoint slot value =
      slotContribution endpoint selected slot value := by
  rw [sourceEndpointContribution_eq_tableMLEValue,
    tableMLEValue_booleanTracePoint]

#print axioms sourceEndpointContribution_eq_tableMLEValue
#print axioms sourceEndpointContribution_boolean
end AspisV8Completion.SelectedCopySingleEndpoint
