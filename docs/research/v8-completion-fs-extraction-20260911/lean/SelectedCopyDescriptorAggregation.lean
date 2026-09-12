import SelectedCopySingleEndpoint

/-! Exact aggregation of the selected 136 Copy descriptors.

The source loop visits every literal link once and calls `accumulate_endpoint`
for its producer and consumer.  This leaf proves that those four slot-valued
linear forms are exactly the multilinear evaluations of the corresponding
fields of `SelectedCopyLayoutRows.sourceRows`.  It also records the signed
producer-minus-consumer value functional without collapsing the two slots
needed by `copy_residual`.

The fourteen-pattern Rust compressor is deliberately not modeled here:
`compressed` is still the independently specified literal pattern expression.
Thus this closes descriptor aggregation, while leaving the compressor-to-
`compressed` refinement as a separate source seam. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.SelectedCopyDescriptorAggregation
open scoped BigOperators
open AspisV8.SelectedCopyLayout
open AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8Completion.SelectedSelectorToSemanticWeight
open AspisV8Completion.SelectedCopyActiveExecutable
open AspisV8Completion.SelectedCopySingleEndpoint

variable {K : Type*} [Field K] [DecidableEq K]

/-- The literal effect of all 136 calls to one side/slot of
`accumulate_endpoint`. -/
def sourceEndpointAggregate (point : Fin 10 → K)
    (endpoint : Fin 136 → Endpoint) (value : Fin 136 → K)
    (slot : Fin 2) : K :=
  ∑ index : Fin 136,
    sourceEndpointContribution point (endpoint index) slot (value index)

/-- Summing the 136 endpoint updates commutes exactly with the selected row
MLE.  No layout, callback, acceptance, or source-equality premise is used. -/
theorem sourceEndpointAggregate_eq_tableMLEValue (point : Fin 10 → K)
    (endpoint : Fin 136 → Endpoint) (value : Fin 136 → K)
    (slot : Fin 2) :
    sourceEndpointAggregate point endpoint value slot =
      tableMLEValue point (fun row => gather endpoint value row slot) := by
  classical
  unfold sourceEndpointAggregate tableMLEValue gather
  calc
    (∑ index : Fin 136,
        sourceEndpointContribution point (endpoint index) slot (value index)) =
        ∑ index : Fin 136, ∑ row : Fin 1024,
          mleRowWeight point row *
            slotContribution (endpoint index) row slot (value index) := by
      apply Finset.sum_congr rfl
      intro index _
      rw [sourceEndpointContribution_eq_tableMLEValue]
      rfl
    _ = ∑ row : Fin 1024, ∑ index : Fin 136,
          mleRowWeight point row *
            slotContribution (endpoint index) row slot (value index) :=
      Finset.sum_comm
    _ = ∑ row : Fin 1024,
          mleRowWeight point row *
            ∑ index : Fin 136,
              slotContribution (endpoint index) row slot (value index) := by
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.mul_sum]

def producerValues (table : Table K) (lambda : K)
    (point : Fin 10 → K) (slot : Fin 2) : K :=
  sourceEndpointAggregate point
    (fun index => (sourceLinks index).producer)
    (fun index => compressed table lambda index (sourceLinks index).producer)
    slot

def producerWeights (variant : AspisV8.SelectedWeightedCopyCore.Variant)
    (appendIndex : Nat) (point : Fin 10 → K) (slot : Fin 2) : K :=
  sourceEndpointAggregate point
    (fun index => (sourceLinks index).producer)
    (AspisV8.SelectedWeightedCopyRows.selectedWeight variant appendIndex)
    slot

def consumerValues (table : Table K) (lambda : K)
    (point : Fin 10 → K) (slot : Fin 2) : K :=
  sourceEndpointAggregate point
    (fun index => (sourceLinks index).consumer)
    (fun index => compressed table lambda index (sourceLinks index).consumer)
    slot

def consumerWeights (variant : AspisV8.SelectedWeightedCopyCore.Variant)
    (appendIndex : Nat) (point : Fin 10 → K) (slot : Fin 2) : K :=
  sourceEndpointAggregate point
    (fun index => (sourceLinks index).consumer)
    (AspisV8.SelectedWeightedCopyRows.selectedWeight variant appendIndex)
    slot

theorem producerValues_eq_sourceRows (table : Table K) (lambda : K)
    (variant : AspisV8.SelectedWeightedCopyCore.Variant) (appendIndex : Nat)
    (point : Fin 10 → K) (slot : Fin 2) :
    producerValues table lambda point slot =
      tableMLEValue point (fun row =>
        (sourceRows table lambda variant appendIndex row).producerValue slot) := by
  exact sourceEndpointAggregate_eq_tableMLEValue point _ _ slot

theorem producerWeights_eq_sourceRows (table : Table K) (lambda : K)
    (variant : AspisV8.SelectedWeightedCopyCore.Variant) (appendIndex : Nat)
    (point : Fin 10 → K) (slot : Fin 2) :
    producerWeights variant appendIndex point slot =
      tableMLEValue point (fun row =>
        (sourceRows table lambda variant appendIndex row).producerWeight slot) := by
  exact sourceEndpointAggregate_eq_tableMLEValue point _ _ slot

theorem consumerValues_eq_sourceRows (table : Table K) (lambda : K)
    (variant : AspisV8.SelectedWeightedCopyCore.Variant) (appendIndex : Nat)
    (point : Fin 10 → K) (slot : Fin 2) :
    consumerValues table lambda point slot =
      tableMLEValue point (fun row =>
        (sourceRows table lambda variant appendIndex row).consumerValue slot) := by
  exact sourceEndpointAggregate_eq_tableMLEValue point _ _ slot

theorem consumerWeights_eq_sourceRows (table : Table K) (lambda : K)
    (variant : AspisV8.SelectedWeightedCopyCore.Variant) (appendIndex : Nat)
    (point : Fin 10 → K) (slot : Fin 2) :
    consumerWeights variant appendIndex point slot =
      tableMLEValue point (fun row =>
        (sourceRows table lambda variant appendIndex row).consumerWeight slot) := by
  exact sourceEndpointAggregate_eq_tableMLEValue point _ _ slot

/-- The signed producer-minus-consumer descriptor value, retaining the slot
index used later by the rational Copy residual. -/
def signedValues (table : Table K) (lambda : K)
    (point : Fin 10 → K) (slot : Fin 2) : K :=
  producerValues table lambda point slot - consumerValues table lambda point slot

theorem signedValues_eq_sourceRows (table : Table K) (lambda : K)
    (variant : AspisV8.SelectedWeightedCopyCore.Variant) (appendIndex : Nat)
    (point : Fin 10 → K) (slot : Fin 2) :
    signedValues table lambda point slot =
      tableMLEValue point (fun row =>
        (sourceRows table lambda variant appendIndex row).producerValue slot -
          (sourceRows table lambda variant appendIndex row).consumerValue slot) := by
  rw [signedValues, producerValues_eq_sourceRows table lambda variant appendIndex,
    consumerValues_eq_sourceRows table lambda variant appendIndex]
  unfold tableMLEValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro row _
  ring

/-- The fifth public output of the source evaluator is the already-proved
literal active-mask functional. -/
theorem active_eq_sourceActiveFlat (point : Fin 10 → K) :
    rustSelectedCopyActive point =
      tableMLEValue point
        (AspisV8Completion.SelectedCopyActiveFlat.activeIndicator (K := K)) := by
  rw [rustSelectedCopyActive_eq_sourceActiveFlat,
    AspisV8Completion.SelectedCopyActiveFlat.sourceActiveFlat_eq_tableMLEValue]

#print axioms sourceEndpointAggregate_eq_tableMLEValue
#print axioms producerValues_eq_sourceRows
#print axioms producerWeights_eq_sourceRows
#print axioms consumerValues_eq_sourceRows
#print axioms consumerWeights_eq_sourceRows
#print axioms signedValues_eq_sourceRows
#print axioms active_eq_sourceActiveFlat
end AspisV8Completion.SelectedCopyDescriptorAggregation
