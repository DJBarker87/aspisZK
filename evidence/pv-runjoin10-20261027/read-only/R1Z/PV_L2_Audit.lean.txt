import R1Z.PV_L2_F3Absorption
import R1Z.PV_L2_F3Adaptive
import R1Z.PV_L2_F3Blocks
import R1Z.PV_L2_F3CompletionLaw
import R1Z.PV_L2_F3CountedArrays
import R1Z.PV_L2_F3CountedErasure
import R1Z.PV_L2_F3CountedFibres
import R1Z.PV_L2_F3Disintegration
import R1Z.PV_L2_F3EntropyJoin
import R1Z.PV_L2_F3EntropyPrefix
import R1Z.PV_L2_F3Law
import R1Z.PV_L2_F3Pair
import R1Z.PV_L2_F3Recorded
import R1Z.PV_L2_F3Schedule
import R1Z.PV_L2_F3SeedObstruction
import R1Z.PV_L2_F3SourceArrays
import R1Z.PV_L2_F3SourceBudget
import R1Z.PV_L2_F3SourceCounts
import R1Z.PV_L2_F3SourceJoint
import R1Z.PV_L2_F3Tape
import R1Z.PV_L2_F3WordCarrier
import R1Z.PV_L2_F3WordStream
import R1Z.PV_L2_F3Words
import R1Z.PV_L2_F5
import R1Z.PV_L2_F5Absorption
import R1Z.PV_L2_F5Machine
import R1Z.PV_L2_F5Transport
import R1Z.PV_L2_F6Dot
import R1Z.PV_L2_F6DotStep
import R1Z.PV_L2_F6Image
import R1Z.PV_L2_F6ImageStep
import R1Z.PV_L2_F6KDot
import R1Z.PV_L2_F6KDotStep
import R1Z.PV_L2_F6Openings
import R1Z.PV_L2_F6Pivot
import R1Z.PV_L2_F6Product
import R1Z.PV_L2_F6ProductOuterStep
import R1Z.PV_L2_F6ProductRow
import R1Z.PV_L2_F6ProductStep
import R1Z.PV_L2_F6Sharing
import R1Z.PV_L2_Headline
import R1Z.PV_L2_HeadlineF3
import R1Z.PV_L2_Record
import R1Z.PV_L2_RecordBind

/-! One final focused import/axioms audit of the new proof cone.
This is not the frozen deployment manifest: native full trace joins remain open. -/

#print axioms R1Z.PV_L2_F3Absorption.mean_congr_instances
#print axioms R1Z.PV_L2_F3Absorption.source_count_absorption
#print axioms R1Z.PV_L2_F3Adaptive.index_preserved
#print axioms R1Z.PV_L2_F3Adaptive.permute_inverse
#print axioms R1Z.PV_L2_F3Adaptive.relabel_inverse
#print axioms R1Z.PV_L2_F3Adaptive.streamEquiv
#print axioms R1Z.PV_L2_F3Adaptive.acceptance_history
#print axioms R1Z.PV_L2_F3Adaptive.uniform_transport
#print axioms R1Z.PV_L2_F3Blocks.precompose_card
#print axioms R1Z.PV_L2_F3Blocks.word_arrays_fibres
#print axioms R1Z.PV_L2_F3Blocks.block_fibres
#print axioms R1Z.PV_L2_F3Blocks.blocks_joint_law
#print axioms R1Z.PV_L2_F3CompletionLaw.padding_uniform
#print axioms R1Z.PV_L2_F3CompletionLaw.complete_uniform
#print axioms R1Z.PV_L2_F3CountedArrays.split
#print axioms R1Z.PV_L2_F3CountedArrays.split_values
#print axioms R1Z.PV_L2_F3CountedArrays.split_counts
#print axioms R1Z.PV_L2_F3CountedArrays.arrays_erases
#print axioms R1Z.PV_L2_F3CountedArrays.arrays_equal_fibres
#print axioms R1Z.PV_L2_F3CountedErasure.counted_erases
#print axioms R1Z.PV_L2_F3CountedErasure.actual_word_conditioned
#print axioms R1Z.PV_L2_F3CountedFibres.tagged_card
#print axioms R1Z.PV_L2_F3CountedFibres.card_rec
#print axioms R1Z.PV_L2_F3CountedFibres.conditional_equal_fibres
#print axioms R1Z.PV_L2_F3Disintegration.posterior_uniform
#print axioms R1Z.PV_L2_F3Disintegration.conditional_kernel
#print axioms R1Z.PV_L2_F3EntropyJoin.entropy_count_absorption
#print axioms R1Z.PV_L2_F3EntropyPrefix.coupling
#print axioms R1Z.PV_L2_F3EntropyPrefix.actual_entropy_preserved
#print axioms R1Z.PV_L2_F3EntropyPrefix.candidate_history_preserved
#print axioms R1Z.PV_L2_F3EntropyPrefix.entropy_words_joint
#print axioms R1Z.PV_L2_F3Law.law_card
#print axioms R1Z.PV_L2_F3Law.conditional_relabel
#print axioms R1Z.PV_L2_F3Law.conditional_test
#print axioms R1Z.PV_L2_F3Pair.fibre_product
#print axioms R1Z.PV_L2_F3Pair.pair_fibres
#print axioms R1Z.PV_L2_F3Pair.pair_erases
#print axioms R1Z.PV_L2_F3Pair.pair_joint_law
#print axioms R1Z.PV_L2_F3Recorded.scalar_erases
#print axioms R1Z.PV_L2_F3Recorded.source_scalar_erases
#print axioms R1Z.PV_L2_F3Recorded.collect_erases
#print axioms R1Z.PV_L2_F3Recorded.qm31_erases
#print axioms R1Z.PV_L2_F3Schedule.scalar_control
#print axioms R1Z.PV_L2_F3Schedule.scalar_permute
#print axioms R1Z.PV_L2_F3Schedule.tower_permute
#print axioms R1Z.PV_L2_F3Schedule.tower_refills
#print axioms R1Z.PV_L2_F3SeedObstruction.raw_good
#print axioms R1Z.PV_L2_F3SeedObstruction.first_zero
#print axioms R1Z.PV_L2_F3SeedObstruction.first_one
#print axioms R1Z.PV_L2_F3SeedObstruction.lifted_position_changes
#print axioms R1Z.PV_L2_F3SeedObstruction.old_l1_still_equal
#print axioms R1Z.PV_L2_F3SourceArrays.initial_model
#print axioms R1Z.PV_L2_F3SourceArrays.splitList_values
#print axioms R1Z.PV_L2_F3SourceArrays.source_arrays
#print axioms R1Z.PV_L2_F3SourceBudget.source_pair
#print axioms R1Z.PV_L2_F3SourceBudget.masking
#print axioms R1Z.PV_L2_F3SourceBudget.entropy
#print axioms R1Z.PV_L2_F3SourceCounts.counted_no_values
#print axioms R1Z.PV_L2_F3SourceCounts.counted_list_step
#print axioms R1Z.PV_L2_F3SourceCounts.source_model
#print axioms R1Z.PV_L2_F3SourceJoint.source_observed
#print axioms R1Z.PV_L2_F3SourceJoint.source_owned
#print axioms R1Z.PV_L2_F3Tape.outputEquiv
#print axioms R1Z.PV_L2_F3Tape.quotient_erases
#print axioms R1Z.PV_L2_F3Tape.owned_erases
#print axioms R1Z.PV_L2_F3Tape.observed_fibres
#print axioms R1Z.PV_L2_F3Tape.owned_joint_law
#print axioms R1Z.PV_L2_F3WordCarrier.splitWord
#print axioms R1Z.PV_L2_F3WordCarrier.split_permute
#print axioms R1Z.PV_L2_F3WordCarrier.high_bit_preserved
#print axioms R1Z.PV_L2_F3WordCarrier.rejection_preserved
#print axioms R1Z.PV_L2_F3WordCarrier.accepted_permute
#print axioms R1Z.PV_L2_F3WordStream.splitStream
#print axioms R1Z.PV_L2_F3WordStream.split_stream_permute
#print axioms R1Z.PV_L2_F3WordStream.high_bits_preserved
#print axioms R1Z.PV_L2_F3WordStream.rejection_history_preserved
#print axioms R1Z.PV_L2_F3WordStream.actual_word_uniform
#print axioms R1Z.PV_L2_F3Words.cellEquiv
#print axioms R1Z.PV_L2_F3Words.accepts_permute
#print axioms R1Z.PV_L2_F3Words.control_permute
#print axioms R1Z.PV_L2_F5.instrumented_erases
#print axioms R1Z.PV_L2_F5.history_prefix
#print axioms R1Z.PV_L2_F5Absorption.fixed_coins_joint
#print axioms R1Z.PV_L2_F5Machine.execute_erases
#print axioms R1Z.PV_L2_F5Machine.execute_history
#print axioms R1Z.PV_L2_F5Machine.comparisons_bounded
#print axioms R1Z.PV_L2_F5Machine.source_loop_record
#print axioms R1Z.PV_L2_F5Transport.real_to_lazy
#print axioms R1Z.PV_L2_F5Transport.lazy_to_middle
#print axioms R1Z.PV_L2_F5Transport.completion_joint
#print axioms R1Z.PV_L2_F6Dot.loop_erases
#print axioms R1Z.PV_L2_F6Dot.dot_erases
#print axioms R1Z.PV_L2_F6DotStep.recorded_erases
#print axioms R1Z.PV_L2_F6DotStep.unroll
#print axioms R1Z.PV_L2_F6DotStep.increment
#print axioms R1Z.PV_L2_F6Image.loop_erases
#print axioms R1Z.PV_L2_F6Image.image_erases
#print axioms R1Z.PV_L2_F6ImageStep.recorded_erases
#print axioms R1Z.PV_L2_F6ImageStep.unroll
#print axioms R1Z.PV_L2_F6ImageStep.increment
#print axioms R1Z.PV_L2_F6KDot.loop_erases
#print axioms R1Z.PV_L2_F6KDot.kdot_erases
#print axioms R1Z.PV_L2_F6KDotStep.recorded_erases
#print axioms R1Z.PV_L2_F6KDotStep.unroll
#print axioms R1Z.PV_L2_F6KDotStep.increment
#print axioms R1Z.PV_L2_F6Openings.opens_queries
#print axioms R1Z.PV_L2_F6Openings.parser_prefix_opens
#print axioms R1Z.PV_L2_F6Openings.parser_queries
#print axioms R1Z.PV_L2_F6Pivot.recorded_erases
#print axioms R1Z.PV_L2_F6Pivot.unroll
#print axioms R1Z.PV_L2_F6Pivot.increment
#print axioms R1Z.PV_L2_F6Pivot.loop_erases
#print axioms R1Z.PV_L2_F6Pivot.piv_erases
#print axioms R1Z.PV_L2_F6Product.loop_erases
#print axioms R1Z.PV_L2_F6Product.product_erases
#print axioms R1Z.PV_L2_F6ProductOuterStep.recorded_erases
#print axioms R1Z.PV_L2_F6ProductOuterStep.unroll
#print axioms R1Z.PV_L2_F6ProductOuterStep.increment
#print axioms R1Z.PV_L2_F6ProductRow.loop_erases
#print axioms R1Z.PV_L2_F6ProductRow.row_erases
#print axioms R1Z.PV_L2_F6ProductStep.recorded_erases
#print axioms R1Z.PV_L2_F6ProductStep.unroll
#print axioms R1Z.PV_L2_F6ProductStep.increment
#print axioms R1Z.PV_L2_F6Sharing.cursor_joint
#print axioms R1Z.PV_L2_F6Sharing.singleton_layer
#print axioms R1Z.PV_L2_F6Sharing.singleton_count
#print axioms R1Z.PV_L2_F6Sharing.request_depths
#print axioms R1Z.PV_L2_F6Sharing.payload_erasure
#print axioms R1Z.PV_L2_Headline.deployed_parser
#print axioms R1Z.PV_L2_Headline.deployed_source_carrier
#print axioms R1Z.PV_L2_Headline.real_to_lazy_actual
#print axioms R1Z.PV_L2_Headline.absorption_actual
#print axioms R1Z.PV_L2_HeadlineF3.absorption_actual
#print axioms R1Z.PV_L2_Record.operation_bind_value
#print axioms R1Z.PV_L2_Record.pure_value
#print axioms R1Z.PV_L2_Record.bind_value
#print axioms R1Z.PV_L2_Record.operation_value
#print axioms R1Z.PV_L2_Record.fail_prefix
#print axioms R1Z.PV_L2_Record.div_prefix
#print axioms R1Z.PV_L2_RecordBind.erase_bind
