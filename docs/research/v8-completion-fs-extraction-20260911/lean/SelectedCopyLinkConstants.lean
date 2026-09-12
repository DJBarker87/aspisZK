import SelectedCopyPatternValuesLiteral
import SelectedCopyLinkBalance

/-! Finite correspondence for the selected Rust `COPY_LINKS` table.

The lists below are the literal field projections of
`pair_forest_copy_terminal_constants.rs`, not values computed from
`sourceLinks`.  Endpoint row/slot pairs are encoded as `2*row+slot`, matching
the existing independently checked lookup-key convention.  The theorems check
all 136 positions and then derive the selected field weight for every variant
and append index.

This is a source transcription certificate, not a Rust extraction theorem:
future literal-source refinement must still establish that these lists are the
arrays loaded by the compiled Rust execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000
set_option maxHeartbeats 1000000
namespace AspisV8Completion.SelectedCopyLinkConstants
open AspisV8.SelectedCopyLayout
open AspisV8.SelectedCopyLinkBalance
open AspisV8.SelectedWeightedCopyCore
open AspisV8.SelectedWeightedCopyRows

def rustTags : List Nat := [
  1124073472,1124073473,1124073474,1124073475,1124073476,1124073477,1124073478,1124073479,
  1124073480,1124073481,1124073482,1124073483,1124073484,1124073485,1124073486,1124073487,
  1124073488,1124073489,1124073490,1124073491,1124073492,1124073493,1124073494,1124073495,
  1124073496,1124073497,1124073498,1124073499,1124073500,1124073501,1124073502,1124073503,
  1124073504,1124073505,1124073506,1124073507,1124073508,1124073509,1124073510,1124073511,
  1124073512,1124073513,1124073514,1124073515,1124073516,1124073517,1124073518,1124073519,
  1124073520,1124073521,1124073522,1124073523,1124073524,1124073525,1124073526,1124073527,
  1124073528,1124073529,1124073530,1124073531,1124073532,1124073533,1124073534,1124073535,
  1124073536,1124073537,1124073538,1124073539,1124073540,1124073541,1124073542,1124073543,
  1124073544,1124073545,1124073546,1124073547,1124073548,1124073549,1124073550,1124073551,
  1124073552,1124073553,1124073554,1124073555,1124073556,1124073557,1124073558,1124073559,
  1124073560,1124073561,1124073562,1124073563,1124073564,1124073565,1124073566,1124073567,
  1124073568,1124073569,1124073570,1124073571,1124073572,1124073573,1124073574,1124073575,
  1124073576,1124073577,1124073578,1124073579,1124073580,1124073581,1124073582,1124073583,
  1124073584,1124073585,1124073586,1124073587,1124073588,1124073589,1124073590,1124073591,
  1124073592,1124073593,1124073594,1124073595,1124073596,1124073597,1124073598,1124073599,
  1124073600,1124073601,1124073602,1124073603,1124073604,1124073605,1124073606,1124073607]

def rustWeightKinds : List Nat := [
  0,0,0,1,1,0,0,0,0,0,0,0,1,0,0,0, 0,0,0,0,1,1,2,0,3,4,3,4,3,4,3,4,
  3,4,3,4,3,4,3,4,3,4,3,4,3,4,3,4, 3,4,3,4,3,4,3,4,3,4,3,4,3,4,3,4,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0]

def rustWeightLevels : List Nat := [
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,1,1,2,2,3,3,
  4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11, 12,12,13,13,14,14,15,15,16,16,17,17,18,18,19,19,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0]

def rustProducerPatterns : List Nat := [
  0,0,0,0,0,0,0,1,1,2,4,6,6,6,7,7, 7,9,10,6,1,1,1,11,1,1,1,1,1,1,1,1,
  1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1, 1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
  1,1,13,1,1,13,1,1,13,1,1,13,1,1,13,1, 1,13,1,1,13,1,1,13,1,1,13,1,1,13,1,1,
  13,1,1,13,1,1,13,1,1,13,1,1,13,1,1,13, 1,1,13,1,1,13,1,1,13,1,1,13,1,1,13,1,
  1,13,1,1,13,1,1,13]

def rustConsumerPatterns : List Nat := [
  0,0,0,0,0,0,0,1,1,3,5,7,7,7,6,8, 8,6,11,7,11,1,1,10,1,10,1,10,1,10,1,10,
  1,10,1,10,1,10,1,10,1,10,1,10,1,10,1,10, 1,10,1,10,1,10,1,10,1,10,1,10,1,10,1,10,
  12,1,10,12,1,10,12,1,10,12,1,10,12,1,10,12, 1,10,12,1,10,12,1,10,12,1,10,12,1,10,12,1,
  10,12,1,10,12,1,10,12,1,10,12,1,10,12,1,10, 12,1,10,12,1,10,12,1,10,12,1,10,12,1,10,12,
  1,10,12,1,10,12,1,10]

/-- No `getD` fallback is reachable at a selected link index. -/
theorem rust_projection_lengths :
    producerKeys.length = 136 ∧ consumerKeys.length = 136 ∧
    rustTags.length = 136 ∧ rustWeightKinds.length = 136 ∧
    rustWeightLevels.length = 136 ∧ rustProducerPatterns.length = 136 ∧
    rustConsumerPatterns.length = 136 := by
  decide

def at136 (values : List Nat) (index : Fin 136) : Nat := values.getD index.val 0

def rustProducerKey (index : Fin 136) : Nat := at136 producerKeys index
def rustConsumerKey (index : Fin 136) : Nat := at136 consumerKeys index
def rustTag (index : Fin 136) : Nat := at136 rustTags index
def rustWeightKindCode (index : Fin 136) : Nat := at136 rustWeightKinds index
def rustWeightLevel (index : Fin 136) : Nat := at136 rustWeightLevels index
def rustProducerPattern (index : Fin 136) : Nat := at136 rustProducerPatterns index
def rustConsumerPattern (index : Fin 136) : Nat := at136 rustConsumerPatterns index

def decodeRustWeightKind (code level : Nat) : WeightKind :=
  match code with
  | 0 => .one
  | 1 => .transfer
  | 2 => .withdrawal
  | 3 => .appendLeft level
  | 4 => .appendRight level
  | _ => .one

def selectedKindCode : WeightKind → Nat
  | .one => 0
  | .transfer => 1
  | .withdrawal => 2
  | .appendLeft _ => 3
  | .appendRight _ => 4

def selectedKindLevel : WeightKind → Nat
  | .appendLeft level | .appendRight level => level
  | _ => 0

theorem decode_selected_kind (kind : WeightKind) :
    decodeRustWeightKind (selectedKindCode kind) (selectedKindLevel kind) = kind := by
  cases kind <;> rfl

theorem rust_link_fields_eq_selected : ∀ index : Fin 136,
    rustProducerKey index = endpointKey (sourceLinks index).producer ∧
    rustConsumerKey index = endpointKey (sourceLinks index).consumer ∧
    rustProducerPattern index = (sourceLinks index).producer.pattern.val ∧
    rustConsumerPattern index = (sourceLinks index).consumer.pattern.val ∧
    rustTag index = selectedTag index ∧
    rustWeightKindCode index = selectedKindCode (selectedKind index) ∧
    rustWeightLevel index = selectedKindLevel (selectedKind index) := by
  intro index
  fin_cases index <;> decide

theorem rust_weight_kind_eq_selected (index : Fin 136) :
    decodeRustWeightKind (rustWeightKindCode index) (rustWeightLevel index) =
      selectedKind index := by
  rw [(rust_link_fields_eq_selected index).2.2.2.2.2.1,
    (rust_link_fields_eq_selected index).2.2.2.2.2.2]
  exact decode_selected_kind (selectedKind index)

theorem rust_producer_row_eq_selected (index : Fin 136) :
    rustProducerKey index / 2 = (sourceLinks index).producer.row.val := by
  have fields := rust_link_fields_eq_selected index
  rw [fields.1, endpointKey]
  omega

theorem rust_producer_slot_eq_selected (index : Fin 136) :
    rustProducerKey index % 2 = (sourceLinks index).producer.slot.val := by
  have fields := rust_link_fields_eq_selected index
  rw [fields.1, endpointKey]
  omega

theorem rust_consumer_row_eq_selected (index : Fin 136) :
    rustConsumerKey index / 2 = (sourceLinks index).consumer.row.val := by
  have fields := rust_link_fields_eq_selected index
  rw [fields.2.1, endpointKey]
  omega

theorem rust_consumer_slot_eq_selected (index : Fin 136) :
    rustConsumerKey index % 2 = (sourceLinks index).consumer.slot.val := by
  have fields := rust_link_fields_eq_selected index
  rw [fields.2.1, endpointKey]
  omega

def rustPublicWeight {K : Type*} [Zero K] [One K]
    (variant : Variant) (appendIndex : Nat) (index : Fin 136) : K :=
  publicWeight variant appendIndex
    (decodeRustWeightKind (rustWeightKindCode index) (rustWeightLevel index))

/-- Stronger than a bounded "legal append index" statement: the literal
kind/level dispatch agrees for every natural append index and both variants. -/
theorem rustPublicWeight_eq_selectedWeight {K : Type*} [Field K]
    (variant : Variant) (appendIndex : Nat) (index : Fin 136) :
    rustPublicWeight (K := K) variant appendIndex index =
      selectedWeight variant appendIndex index := by
  unfold rustPublicWeight selectedWeight
  rw [rust_weight_kind_eq_selected]

#print axioms rust_link_fields_eq_selected
#print axioms rust_projection_lengths
#print axioms rust_weight_kind_eq_selected
#print axioms rust_producer_row_eq_selected
#print axioms rust_producer_slot_eq_selected
#print axioms rust_consumer_row_eq_selected
#print axioms rust_consumer_slot_eq_selected
#print axioms rustPublicWeight_eq_selectedWeight
end AspisV8Completion.SelectedCopyLinkConstants
