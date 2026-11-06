import NIU_COMBINED_IMPORT
import NGK_COMBINED_IMPORT
import NJB_AbortPrefix
import NJB_Absorption
import NJB_AbsorptionAssociation
import NJB_AbsorptionCuts
import NJB_AbsorptionLane
import NJB_AbsorptionScales
import NJB_ActiveAssociation
import NJB_ActiveModel
import NJB_ActiveRawHigh
import NJB_ActiveRawLow
import NJB_ActiveReference
import NJB_ArrayCarrier
import NJB_ArrayInspect
import NJB_ArrayReads
import NJB_BasicInspect
import NJB_CopyResidual
import NJB_CutDischarge
import NJB_Cuts
import NJB_DecodeInjective
import NJB_FieldInventory
import NJB_MaskTable
import NJB_ModelInventory
import NJB_PackLaw
import NJB_PackLinearity
import NJB_PatternArray
import NJB_PatternCuts
import NJB_PatternReference
import NJB_PreparedCarrier
import NJB_PreparedLaws
import NJB_SemanticPublic
import NJB_SharedReference
import NJB_StateUpdates
import NJB_StubLaws
import NJB_TagRaw
import NJB_TagReduce
import NJB_Traverse
import NJB_Words

#print axioms AspisR1.RPx_Deployed.deployed
#check AspisR1.NJB_AbortPrefix.append
#print axioms AspisR1.NJB_AbortPrefix.append
#check AspisR1.NJB_AbortPrefix.div
#print axioms AspisR1.NJB_AbortPrefix.div
#check AspisR1.NJB_AbortPrefix.fail
#print axioms AspisR1.NJB_AbortPrefix.fail
#check AspisR1.NJB_Absorption.result
#print axioms AspisR1.NJB_Absorption.result
#check AspisR1.NJB_Absorption.size
#print axioms AspisR1.NJB_Absorption.size
#check AspisR1.NJB_AbsorptionAssociation.result
#print axioms AspisR1.NJB_AbsorptionAssociation.result
#check AspisR1.NJB_AbsorptionCuts.discharge
#print axioms AspisR1.NJB_AbsorptionCuts.discharge
#check AspisR1.NJB_AbsorptionLane.model_eq_literal
#print axioms AspisR1.NJB_AbsorptionLane.model_eq_literal
#check AspisR1.NJB_AbsorptionLane.result
#print axioms AspisR1.NJB_AbsorptionLane.result
#check AspisR1.NJB_AbsorptionScales.result
#print axioms AspisR1.NJB_AbsorptionScales.result
#check AspisR1.NJB_ActiveAssociation.cohort
#print axioms AspisR1.NJB_ActiveAssociation.cohort
#check AspisR1.NJB_ActiveAssociation.high_same
#print axioms AspisR1.NJB_ActiveAssociation.high_same
#check AspisR1.NJB_ActiveAssociation.index_value
#print axioms AspisR1.NJB_ActiveAssociation.index_value
#check AspisR1.NJB_ActiveAssociation.low_same
#print axioms AspisR1.NJB_ActiveAssociation.low_same
#check AspisR1.NJB_ActiveAssociation.model_same
#print axioms AspisR1.NJB_ActiveAssociation.model_same
#check AspisR1.NJB_ActiveAssociation.result
#print axioms AspisR1.NJB_ActiveAssociation.result
#check AspisR1.NJB_ActiveModel.high_complete
#print axioms AspisR1.NJB_ActiveModel.high_complete
#check AspisR1.NJB_ActiveModel.high_prefix
#print axioms AspisR1.NJB_ActiveModel.high_prefix
#check AspisR1.NJB_ActiveModel.low_prefix
#print axioms AspisR1.NJB_ActiveModel.low_prefix
#check AspisR1.NJB_ActiveModel.result
#print axioms AspisR1.NJB_ActiveModel.result
#check AspisR1.NJB_ActiveRawHigh.run_result
#print axioms AspisR1.NJB_ActiveRawHigh.run_result
#check AspisR1.NJB_ActiveRawHigh.step_result
#print axioms AspisR1.NJB_ActiveRawHigh.step_result
#check AspisR1.NJB_ActiveRawLow.low_sum_result
#print axioms AspisR1.NJB_ActiveRawLow.low_sum_result
#check AspisR1.NJB_ActiveRawLow.run_result
#print axioms AspisR1.NJB_ActiveRawLow.run_result
#check AspisR1.NJB_ActiveRawLow.step_result
#print axioms AspisR1.NJB_ActiveRawLow.step_result
#check AspisR1.NJB_ActiveReference.result
#print axioms AspisR1.NJB_ActiveReference.result
#check AspisR1.NJB_ArrayCarrier.array_cell
#print axioms AspisR1.NJB_ArrayCarrier.array_cell
#check AspisR1.NJB_ArrayCarrier.canonical_array
#print axioms AspisR1.NJB_ArrayCarrier.canonical_array
#check AspisR1.NJB_ArrayCarrier.canonical_cell
#print axioms AspisR1.NJB_ArrayCarrier.canonical_cell
#check AspisR1.NJB_ArrayCarrier.cell_array
#print axioms AspisR1.NJB_ArrayCarrier.cell_array
#check AspisR1.NJB_ArrayReads.read
#print axioms AspisR1.NJB_ArrayReads.read
#check AspisR1.NJB_ArrayReads.value
#print axioms AspisR1.NJB_ArrayReads.value
#check AspisR1.NJB_CopyResidual.result
#print axioms AspisR1.NJB_CopyResidual.result
#check AspisR1.NJB_CutDischarge.high
#print axioms AspisR1.NJB_CutDischarge.high
#check AspisR1.NJB_Cuts.high_next_bound
#print axioms AspisR1.NJB_Cuts.high_next_bound
#check AspisR1.NJB_Cuts.low_count_bound
#print axioms AspisR1.NJB_Cuts.low_count_bound
#check AspisR1.NJB_Cuts.low_count_positive
#print axioms AspisR1.NJB_Cuts.low_count_positive
#check AspisR1.NJB_Cuts.low_next_bound
#print axioms AspisR1.NJB_Cuts.low_next_bound
#check AspisR1.NJB_DecodeInjective.array
#print axioms AspisR1.NJB_DecodeInjective.array
#check AspisR1.NJB_DecodeInjective.list
#print axioms AspisR1.NJB_DecodeInjective.list
#check AspisR1.NJB_DecodeInjective.qm
#print axioms AspisR1.NJB_DecodeInjective.qm
#check AspisR1.NJB_DecodeInjective.word
#print axioms AspisR1.NJB_DecodeInjective.word
#check AspisR1.NJB_MaskTable.source_eq_model
#print axioms AspisR1.NJB_MaskTable.source_eq_model
#check AspisR1.NJB_MaskTable.source_key_eq_model
#print axioms AspisR1.NJB_MaskTable.source_key_eq_model
#check AspisR1.NJB_PackLaw.length
#print axioms AspisR1.NJB_PackLaw.length
#check AspisR1.NJB_PackLaw.qm_raw
#print axioms AspisR1.NJB_PackLaw.qm_raw
#check AspisR1.NJB_PackLaw.result
#print axioms AspisR1.NJB_PackLaw.result
#check AspisR1.NJB_PackLinearity.add
#print axioms AspisR1.NJB_PackLinearity.add
#check AspisR1.NJB_PackLinearity.model
#print axioms AspisR1.NJB_PackLinearity.model
#check AspisR1.NJB_PackLinearity.scale
#print axioms AspisR1.NJB_PackLinearity.scale
#check AspisR1.NJB_PackLinearity.zero
#print axioms AspisR1.NJB_PackLinearity.zero
#check AspisR1.NJB_PatternArray.result
#print axioms AspisR1.NJB_PatternArray.result
#check AspisR1.NJB_PatternArray.size14
#print axioms AspisR1.NJB_PatternArray.size14
#check AspisR1.NJB_PatternArray.size26
#print axioms AspisR1.NJB_PatternArray.size26
#check AspisR1.NJB_PatternArray.size4
#print axioms AspisR1.NJB_PatternArray.size4
#check AspisR1.NJB_PatternArray.state_pack
#print axioms AspisR1.NJB_PatternArray.state_pack
#check AspisR1.NJB_PatternCuts.discharge
#print axioms AspisR1.NJB_PatternCuts.discharge
#check AspisR1.NJB_PatternReference.bounds
#print axioms AspisR1.NJB_PatternReference.bounds
#check AspisR1.NJB_PatternReference.coordinates_values
#print axioms AspisR1.NJB_PatternReference.coordinates_values
#check AspisR1.NJB_PatternReference.group_indices
#print axioms AspisR1.NJB_PatternReference.group_indices
#check AspisR1.NJB_PatternReference.inner_result
#print axioms AspisR1.NJB_PatternReference.inner_result
#check AspisR1.NJB_PatternReference.result
#print axioms AspisR1.NJB_PatternReference.result
#check AspisR1.NJB_PreparedCarrier.ext
#print axioms AspisR1.NJB_PreparedCarrier.ext
#check AspisR1.NJB_PreparedCarrier.size
#print axioms AspisR1.NJB_PreparedCarrier.size
#check AspisR1.NJB_PreparedCarrier.value_words
#print axioms AspisR1.NJB_PreparedCarrier.value_words
#check AspisR1.NJB_PreparedCarrier.words_value
#print axioms AspisR1.NJB_PreparedCarrier.words_value
#check AspisR1.NJB_PreparedLaws.mul_result
#print axioms AspisR1.NJB_PreparedLaws.mul_result
#check AspisR1.NJB_PreparedLaws.new_result
#print axioms AspisR1.NJB_PreparedLaws.new_result
#check AspisR1.NJB_SemanticPublic.result
#print axioms AspisR1.NJB_SemanticPublic.result
#check AspisR1.NJB_SharedReference.lanes_canonical
#print axioms AspisR1.NJB_SharedReference.lanes_canonical
#check AspisR1.NJB_SharedReference.result
#print axioms AspisR1.NJB_SharedReference.result
#check AspisR1.NJB_SharedReference.step_result
#print axioms AspisR1.NJB_SharedReference.step_result
#check AspisR1.NJB_StateUpdates.add_result
#print axioms AspisR1.NJB_StateUpdates.add_result
#check AspisR1.NJB_StateUpdates.mul_add_result
#print axioms AspisR1.NJB_StateUpdates.mul_add_result
#check AspisR1.NJB_StateUpdates.run_result
#print axioms AspisR1.NJB_StateUpdates.run_result
#check AspisR1.NJB_StateUpdates.sum_frame
#print axioms AspisR1.NJB_StateUpdates.sum_frame
#check AspisR1.NJB_StubLaws.qm_add
#print axioms AspisR1.NJB_StubLaws.qm_add
#check AspisR1.NJB_StubLaws.qm_mul
#print axioms AspisR1.NJB_StubLaws.qm_mul
#check AspisR1.NJB_StubLaws.qm_sub
#print axioms AspisR1.NJB_StubLaws.qm_sub
#check AspisR1.NJB_TagRaw.chunk_bound
#print axioms AspisR1.NJB_TagRaw.chunk_bound
#check AspisR1.NJB_TagRaw.four_products_fit
#print axioms AspisR1.NJB_TagRaw.four_products_fit
#check AspisR1.NJB_TagRaw.product
#print axioms AspisR1.NJB_TagRaw.product
#check AspisR1.NJB_TagRaw.product_bound
#print axioms AspisR1.NJB_TagRaw.product_bound
#check AspisR1.NJB_TagRaw.step_bound
#print axioms AspisR1.NJB_TagRaw.step_bound
#check AspisR1.NJB_TagRaw.sum_bound
#print axioms AspisR1.NJB_TagRaw.sum_bound
#check AspisR1.NJB_TagReduce.add
#print axioms AspisR1.NJB_TagReduce.add
#check AspisR1.NJB_TagReduce.reduce
#print axioms AspisR1.NJB_TagReduce.reduce
#check AspisR1.NJB_TagReduce.result
#print axioms AspisR1.NJB_TagReduce.result
#check AspisR1.NJB_Traverse.diverged_head
#print axioms AspisR1.NJB_Traverse.diverged_head
#check AspisR1.NJB_Traverse.failed_head
#print axioms AspisR1.NJB_Traverse.failed_head
#check AspisR1.NJB_Traverse.result
#print axioms AspisR1.NJB_Traverse.result
#check AspisR1.NJB_Words.ext
#print axioms AspisR1.NJB_Words.ext
#check AspisR1.NJB_Words.value_word
#print axioms AspisR1.NJB_Words.value_word
#check AspisR1.NJB_Words.word_value
#print axioms AspisR1.NJB_Words.word_value
