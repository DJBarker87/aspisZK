import SelectedCopyLinkConstants

/-! Complete functional Copy residual from the certified literal projections.

This reconstructs the four arrays accumulated by the selected Rust link loop
from the independently transcribed endpoint, pattern, tag, kind and level
fields.  It then proves that the exact nonlinear two-slot `copy_residual`,
including its public weights, producer/consumer signs, helper and active-mask
multiplier, is the selected row-MLE functional.

This is still a functional source model.  It does not assert that an actual
Rust execution loads these constants or refine Rust machine operations to the
field operations below. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000
set_option maxHeartbeats 1000000
namespace AspisV8Completion.SelectedCopyResidualCallback
open scoped BigOperators
open AspisV8.SelectedCopyLayout
open AspisV8.SelectedCopyLinkBalance
open AspisV8.SelectedCopyLayoutRows
open AspisV8.SelectedSemanticLaneAggregation
open AspisV8.SelectedWeightedCopyCore
open AspisV8.SelectedWeightedCopyRows
open AspisV8Completion.SelectedCopySingleEndpoint
open AspisV8Completion.SelectedCopyDescriptorAggregation
open AspisV8Completion.SelectedCopyPatternValuesLiteral
open AspisV8Completion.SelectedCopyLinkConstants

variable {K : Type*} [Field K] [DecidableEq K]

theorem rustProducerKey_lt (index : Fin 136) : rustProducerKey index < 2048 := by
  rw [(rust_link_fields_eq_selected index).1, endpointKey]
  have rowBound := (sourceLinks index).producer.row.isLt
  have slotBound := (sourceLinks index).producer.slot.isLt
  omega

theorem rustConsumerKey_lt (index : Fin 136) : rustConsumerKey index < 2048 := by
  rw [(rust_link_fields_eq_selected index).2.1, endpointKey]
  have rowBound := (sourceLinks index).consumer.row.isLt
  have slotBound := (sourceLinks index).consumer.slot.isLt
  omega

theorem rustProducerPattern_lt (index : Fin 136) : rustProducerPattern index < 14 := by
  rw [(rust_link_fields_eq_selected index).2.2.1]
  exact (sourceLinks index).producer.pattern.isLt

theorem rustConsumerPattern_lt (index : Fin 136) : rustConsumerPattern index < 14 := by
  rw [(rust_link_fields_eq_selected index).2.2.2.1]
  exact (sourceLinks index).consumer.pattern.isLt

def rustProducerEndpoint (index : Fin 136) : Endpoint where
  row := ⟨rustProducerKey index / 2, by
    have := rustProducerKey_lt index
    omega⟩
  slot := ⟨rustProducerKey index % 2, Nat.mod_lt _ (by decide)⟩
  pattern := ⟨rustProducerPattern index, rustProducerPattern_lt index⟩

def rustConsumerEndpoint (index : Fin 136) : Endpoint where
  row := ⟨rustConsumerKey index / 2, by
    have := rustConsumerKey_lt index
    omega⟩
  slot := ⟨rustConsumerKey index % 2, Nat.mod_lt _ (by decide)⟩
  pattern := ⟨rustConsumerPattern index, rustConsumerPattern_lt index⟩

theorem endpoint_extensionality (left right : Endpoint)
    (row : left.row = right.row) (slot : left.slot = right.slot)
    (pattern : left.pattern = right.pattern) : left = right := by
  cases left
  cases right
  simp_all

theorem rustProducerEndpoint_eq_selected (index : Fin 136) :
    rustProducerEndpoint index = (sourceLinks index).producer := by
  apply endpoint_extensionality
  · apply Fin.ext
    exact rust_producer_row_eq_selected index
  · apply Fin.ext
    exact rust_producer_slot_eq_selected index
  · apply Fin.ext
    exact (rust_link_fields_eq_selected index).2.2.1

theorem rustConsumerEndpoint_eq_selected (index : Fin 136) :
    rustConsumerEndpoint index = (sourceLinks index).consumer := by
  apply endpoint_extensionality
  · apply Fin.ext
    exact rust_consumer_row_eq_selected index
  · apply Fin.ext
    exact rust_consumer_slot_eq_selected index
  · apply Fin.ext
    exact (rust_link_fields_eq_selected index).2.2.2.1

def rustProducerCompressed (table : Table K) (lambda : K)
    (index : Fin 136) : K :=
  (rustTag index : K) +
    rustPatternValueLiteral
      (fun column => table (rustProducerEndpoint index).row column)
      lambda (rustProducerEndpoint index).pattern

def rustConsumerCompressed (table : Table K) (lambda : K)
    (index : Fin 136) : K :=
  (rustTag index : K) +
    rustPatternValueLiteral
      (fun column => table (rustConsumerEndpoint index).row column)
      lambda (rustConsumerEndpoint index).pattern

theorem rustProducerCompressed_eq_selected (table : Table K) (lambda : K)
    (index : Fin 136) :
    rustProducerCompressed table lambda index =
      compressed table lambda index (sourceLinks index).producer := by
  unfold rustProducerCompressed
  rw [rustProducerEndpoint_eq_selected,
    (rust_link_fields_eq_selected index).2.2.2.2.1]
  exact selectedTag_add_rustPatternValueLiteral_eq_compressed table lambda index _

theorem rustConsumerCompressed_eq_selected (table : Table K) (lambda : K)
    (index : Fin 136) :
    rustConsumerCompressed table lambda index =
      compressed table lambda index (sourceLinks index).consumer := by
  unfold rustConsumerCompressed
  rw [rustConsumerEndpoint_eq_selected,
    (rust_link_fields_eq_selected index).2.2.2.2.1]
  exact selectedTag_add_rustPatternValueLiteral_eq_compressed table lambda index _

/-- Exact four accumulators produced by the literal link loop. -/
def rustCopyRow (table : Table K) (lambda : K) (variant : Variant)
    (appendIndex : Nat) (point : Fin 10 → K) : Row K where
  producerValue slot := ∑ index : Fin 136,
    sourceEndpointContribution point (rustProducerEndpoint index) slot
      (rustProducerCompressed table lambda index)
  producerWeight slot := ∑ index : Fin 136,
    sourceEndpointContribution point (rustProducerEndpoint index) slot
      (rustPublicWeight variant appendIndex index)
  consumerValue slot := ∑ index : Fin 136,
    sourceEndpointContribution point (rustConsumerEndpoint index) slot
      (rustConsumerCompressed table lambda index)
  consumerWeight slot := ∑ index : Fin 136,
    sourceEndpointContribution point (rustConsumerEndpoint index) slot
      (rustPublicWeight variant appendIndex index)

/-- MLE row whose four fields are consumed by the selected nonlinear Copy
residual.  The imported `producerValues_eq_sourceRows` and its three sibling
theorems identify these four named functionals with the corresponding row
MLEs without forcing reduction of the 136-entry constants in this leaf. -/
def selectedMLERow (table : Table K) (lambda : K) (variant : Variant)
    (appendIndex : Nat) (point : Fin 10 → K) : Row K where
  producerValue := producerValues table lambda point
  producerWeight := producerWeights variant appendIndex point
  consumerValue := consumerValues table lambda point
  consumerWeight := consumerWeights variant appendIndex point

theorem selectedMLERow_fields_are_sourceMLE (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (point : Fin 10 → K) :
    (∀ slot, (selectedMLERow table lambda variant appendIndex point).producerValue slot =
      tableMLEValue point (fun row =>
        (sourceRows table lambda variant appendIndex row).producerValue slot)) ∧
    (∀ slot, (selectedMLERow table lambda variant appendIndex point).producerWeight slot =
      tableMLEValue point (fun row =>
        (sourceRows table lambda variant appendIndex row).producerWeight slot)) ∧
    (∀ slot, (selectedMLERow table lambda variant appendIndex point).consumerValue slot =
      tableMLEValue point (fun row =>
        (sourceRows table lambda variant appendIndex row).consumerValue slot)) ∧
    (∀ slot, (selectedMLERow table lambda variant appendIndex point).consumerWeight slot =
      tableMLEValue point (fun row =>
        (sourceRows table lambda variant appendIndex row).consumerWeight slot)) := by
  constructor
  · intro slot
    change producerValues table lambda point slot = _
    exact producerValues_eq_sourceRows table lambda variant appendIndex point slot
  constructor
  · intro slot
    change producerWeights variant appendIndex point slot = _
    exact producerWeights_eq_sourceRows table lambda variant appendIndex point slot
  constructor
  · intro slot
    change consumerValues table lambda point slot = _
    exact consumerValues_eq_sourceRows table lambda variant appendIndex point slot
  · intro slot
    change consumerWeights variant appendIndex point slot = _
    exact consumerWeights_eq_sourceRows table lambda variant appendIndex point slot

theorem row_extensionality (left right : Row K)
    (producerValue : left.producerValue = right.producerValue)
    (producerWeight : left.producerWeight = right.producerWeight)
    (consumerValue : left.consumerValue = right.consumerValue)
    (consumerWeight : left.consumerWeight = right.consumerWeight) : left = right := by
  cases left
  cases right
  simp_all

theorem rustCopyRow_producerValue_eq (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (point : Fin 10 → K) (slot : Fin 2) :
    (rustCopyRow table lambda variant appendIndex point).producerValue slot =
      producerValues table lambda point slot := by
  change (∑ index : Fin 136,
      sourceEndpointContribution point (rustProducerEndpoint index) slot
        (rustProducerCompressed table lambda index)) = _
  unfold producerValues sourceEndpointAggregate
  apply Finset.sum_congr rfl
  intro index _
  rw [rustProducerEndpoint_eq_selected, rustProducerCompressed_eq_selected]

theorem rustCopyRow_producerWeight_eq (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (point : Fin 10 → K) (slot : Fin 2) :
    (rustCopyRow table lambda variant appendIndex point).producerWeight slot =
      producerWeights variant appendIndex point slot := by
  change (∑ index : Fin 136,
      sourceEndpointContribution point (rustProducerEndpoint index) slot
        (rustPublicWeight variant appendIndex index)) = _
  unfold producerWeights sourceEndpointAggregate
  apply Finset.sum_congr rfl
  intro index _
  rw [rustProducerEndpoint_eq_selected, rustPublicWeight_eq_selectedWeight]

theorem rustCopyRow_consumerValue_eq (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (point : Fin 10 → K) (slot : Fin 2) :
    (rustCopyRow table lambda variant appendIndex point).consumerValue slot =
      consumerValues table lambda point slot := by
  change (∑ index : Fin 136,
      sourceEndpointContribution point (rustConsumerEndpoint index) slot
        (rustConsumerCompressed table lambda index)) = _
  unfold consumerValues sourceEndpointAggregate
  apply Finset.sum_congr rfl
  intro index _
  rw [rustConsumerEndpoint_eq_selected, rustConsumerCompressed_eq_selected]

theorem rustCopyRow_consumerWeight_eq (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (point : Fin 10 → K) (slot : Fin 2) :
    (rustCopyRow table lambda variant appendIndex point).consumerWeight slot =
      consumerWeights variant appendIndex point slot := by
  change (∑ index : Fin 136,
      sourceEndpointContribution point (rustConsumerEndpoint index) slot
        (rustPublicWeight variant appendIndex index)) = _
  unfold consumerWeights sourceEndpointAggregate
  apply Finset.sum_congr rfl
  intro index _
  rw [rustConsumerEndpoint_eq_selected, rustPublicWeight_eq_selectedWeight]

theorem rustCopyRow_eq_selectedMLERow (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (point : Fin 10 → K) :
    rustCopyRow table lambda variant appendIndex point =
      selectedMLERow table lambda variant appendIndex point := by
  apply row_extensionality <;> funext slot
  · exact rustCopyRow_producerValue_eq table lambda variant appendIndex point slot
  · exact rustCopyRow_producerWeight_eq table lambda variant appendIndex point slot
  · exact rustCopyRow_consumerValue_eq table lambda variant appendIndex point slot
  · exact rustCopyRow_consumerWeight_eq table lambda variant appendIndex point slot

/-- Direct transcription of Rust `copy_residual`, retaining both slots even
when their public weight is zero. -/
def rustCopyResidual (row : Row K) (helper chi : K) : K :=
  let p0 := chi - row.producerValue 0
  let p1 := chi - row.producerValue 1
  let c0 := chi - row.consumerValue 0
  let c1 := chi - row.consumerValue 1
  let pd := p0 * p1
  let cd := c0 * c1
  let pn := row.producerWeight 0 * p1 + row.producerWeight 1 * p0
  let cn := row.consumerWeight 0 * c1 + row.consumerWeight 1 * c0
  pd * (helper * cd + cn) - cd * pn

theorem rustCopyResidual_eq_sourceResidual (row : Row K) (helper chi : K) :
    rustCopyResidual row helper chi = sourceResidual row helper chi := by
  rfl

noncomputable def rustCopyTerminal (table : Table K) (lambda : K) (variant : Variant)
    (appendIndex : Nat) (point : Fin 10 → K) (helper chi : K) : K :=
  AspisV8Completion.SelectedCopyActiveExecutable.rustSelectedCopyActive point *
    rustCopyResidual (rustCopyRow table lambda variant appendIndex point) helper chi

def selectedCopyTerminal (table : Table K) (lambda : K) (variant : Variant)
    (appendIndex : Nat) (point : Fin 10 → K) (helper chi : K) : K :=
  tableMLEValue point
      (AspisV8Completion.SelectedCopyActiveFlat.activeIndicator (K := K)) *
    sourceResidual (selectedMLERow table lambda variant appendIndex point) helper chi

/-- Complete functional callback identity for the Copy lane.  The minus sign
between producer and consumer numerators is inherited literally through
`rustCopyResidual_eq_sourceResidual`; no linearized substitute is used. -/
theorem rustCopyTerminal_eq_selectedCopyTerminal (table : Table K) (lambda : K)
    (variant : Variant) (appendIndex : Nat) (point : Fin 10 → K)
    (helper chi : K) :
    rustCopyTerminal table lambda variant appendIndex point helper chi =
      selectedCopyTerminal table lambda variant appendIndex point helper chi := by
  unfold rustCopyTerminal selectedCopyTerminal
  rw [AspisV8Completion.SelectedCopyDescriptorAggregation.active_eq_sourceActiveFlat,
    rustCopyResidual_eq_sourceResidual, rustCopyRow_eq_selectedMLERow]

#print axioms rustProducerEndpoint_eq_selected
#print axioms rustConsumerEndpoint_eq_selected
#print axioms rustProducerCompressed_eq_selected
#print axioms rustConsumerCompressed_eq_selected
#print axioms rustCopyRow_eq_selectedMLERow
#print axioms selectedMLERow_fields_are_sourceMLE
#print axioms rustCopyResidual_eq_sourceResidual
#print axioms rustCopyTerminal_eq_selectedCopyTerminal
end AspisV8Completion.SelectedCopyResidualCallback
