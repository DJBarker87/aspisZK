import LPb_ByteFold
import LPb_CheckpointAttempts
import LPb_CheckpointFinalValue
import LPb_CheckpointLayout
import LPb_CheckpointNativeGap
import LPb_CheckpointPrefixes
import LPb_CheckpointSequence
import LPb_ClaimFailure
import LPb_ClaimStages
import LPb_CollectLengths
import LPb_FoldStages
import LPb_ListWidths
import LPb_Logged
import LPb_Nonvacuity
import LPb_PayloadWidth
import LPb_PreparedSequence
import LPb_PreparedWitness
import LPb_ResultInversion
set_option autoImplicit false
#check @LPb_ByteFold.scalar_words
#check @LPb_ByteFold.append_spec
#check @LPb_ByteFold.weights_sequence
#check @LPb_ByteFold.word_length
#check @LPb_ByteFold.scalar_length
#check @LPb_ByteFold.scalars_length
#check @LPb_ByteFold.weights64
#check @LPb_CheckpointAttempts.first_failure
#check @LPb_CheckpointAttempts.second_failure
#check @LPb_CheckpointAttempts.successful_stages
#check @LPb_CheckpointFinalValue.finish_value
#check @LPb_CheckpointFinalValue.value
#check @LPb_CheckpointLayout.slice_value
#check @LPb_CheckpointNativeGap.model_trace_bytes
#check @LPb_CheckpointPrefixes.wide_failure
#check @LPb_CheckpointPrefixes.payload_failure
#check @LPb_CheckpointPrefixes.checksum_failure
#check @LPb_CheckpointSequence.checkpoint_model_stages
#check @LPb_CheckpointSequence.erase
#check @LPb_ClaimFailure.stopped_fold
#check @LPb_ClaimFailure.stopped_finish
#check @LPb_ClaimStages.part_model_stages
#check @LPb_ClaimStages.stopped_step
#check @LPb_CollectLengths.none_absorbing
#check @LPb_CollectLengths.length_of_success
#check @LPb_FoldStages.congr
#check @LPb_FoldStages.powers_zero
#check @LPb_FoldStages.powers_one
#check @LPb_FoldStages.powers_next
#check @LPb_FoldStages.powers_seven
#check @LPb_ListWidths.flatMap_length
#check @LPb_ListWidths.array_bytes
#check @LPb_Logged.erase_bind
#check @LPb_Logged.bind_ok
#check @LPb_Logged.bind_failure
#check @LPb_Logged.bind_diverge
#check @LPb_Logged.attempted_failure
#check @LPb_Nonvacuity.query_domain
#check @LPb_Nonvacuity.scalar_index_domain
#check @LPb_Nonvacuity.weight_index_domain
#check @LPb_Nonvacuity.scalar_rejection_domain
#check @LPb_Nonvacuity.attempted_failure_witness
#check @LPb_PayloadWidth.payload_width
#check @LPb_PreparedSequence.prepared_model_stages
#check @LPb_PreparedWitness.powers_length
#check @LPb_PreparedWitness.trace
#check @LPb_ResultInversion.bind_success
#print axioms LPb_ByteFold.scalar_words
#print axioms LPb_ByteFold.append_spec
#print axioms LPb_ByteFold.weights_sequence
#print axioms LPb_ByteFold.word_length
#print axioms LPb_ByteFold.scalar_length
#print axioms LPb_ByteFold.scalars_length
#print axioms LPb_ByteFold.weights64
#print axioms LPb_CheckpointAttempts.first_failure
#print axioms LPb_CheckpointAttempts.second_failure
#print axioms LPb_CheckpointAttempts.successful_stages
#print axioms LPb_CheckpointFinalValue.finish_value
#print axioms LPb_CheckpointFinalValue.value
#print axioms LPb_CheckpointLayout.slice_value
#print axioms LPb_CheckpointNativeGap.model_trace_bytes
#print axioms LPb_CheckpointPrefixes.wide_failure
#print axioms LPb_CheckpointPrefixes.payload_failure
#print axioms LPb_CheckpointPrefixes.checksum_failure
#print axioms LPb_CheckpointSequence.checkpoint_model_stages
#print axioms LPb_CheckpointSequence.erase
#print axioms LPb_ClaimFailure.stopped_fold
#print axioms LPb_ClaimFailure.stopped_finish
#print axioms LPb_ClaimStages.part_model_stages
#print axioms LPb_ClaimStages.stopped_step
#print axioms LPb_CollectLengths.none_absorbing
#print axioms LPb_CollectLengths.length_of_success
#print axioms LPb_FoldStages.congr
#print axioms LPb_FoldStages.powers_zero
#print axioms LPb_FoldStages.powers_one
#print axioms LPb_FoldStages.powers_next
#print axioms LPb_FoldStages.powers_seven
#print axioms LPb_ListWidths.flatMap_length
#print axioms LPb_ListWidths.array_bytes
#print axioms LPb_Logged.erase_bind
#print axioms LPb_Logged.bind_ok
#print axioms LPb_Logged.bind_failure
#print axioms LPb_Logged.bind_diverge
#print axioms LPb_Logged.attempted_failure
#print axioms LPb_Nonvacuity.query_domain
#print axioms LPb_Nonvacuity.scalar_index_domain
#print axioms LPb_Nonvacuity.weight_index_domain
#print axioms LPb_Nonvacuity.scalar_rejection_domain
#print axioms LPb_Nonvacuity.attempted_failure_witness
#print axioms LPb_PayloadWidth.payload_width
#print axioms LPb_PreparedSequence.prepared_model_stages
#print axioms LPb_PreparedWitness.powers_length
#print axioms LPb_PreparedWitness.trace
#print axioms LPb_ResultInversion.bind_success
