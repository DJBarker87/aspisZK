# Final focused axioms audit

`PV_L2_Audit`, J20200: exit 0; 140 printed declarations. Exact output and
resource/source/dependency receipt: [J20200](J20200/receipt.json).
Empty means Lean reported no axioms. Failed elaboration prints in earlier
receipts are not proof results. No `sorryAx` occurs in this successful audit.

| Declaration | `#print axioms` |
|---|---|
| `R1Z.PV_L2_F3Absorption.mean_congr_instances` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Absorption.source_count_absorption` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Adaptive.index_preserved` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Adaptive.permute_inverse` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3Adaptive.relabel_inverse` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Adaptive.streamEquiv` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Adaptive.acceptance_history` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Adaptive.uniform_transport` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Blocks.precompose_card` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Blocks.word_arrays_fibres` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Blocks.block_fibres` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Blocks.blocks_joint_law` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3CompletionLaw.padding_uniform` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3CompletionLaw.complete_uniform` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3CountedArrays.split` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3CountedArrays.split_values` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3CountedArrays.split_counts` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3CountedArrays.arrays_erases` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3CountedArrays.arrays_equal_fibres` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3CountedErasure.counted_erases` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3CountedErasure.actual_word_conditioned` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3CountedFibres.tagged_card` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3CountedFibres.card_rec` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3CountedFibres.conditional_equal_fibres` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Disintegration.posterior_uniform` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Disintegration.conditional_kernel` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3EntropyJoin.entropy_count_absorption` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3EntropyPrefix.coupling` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3EntropyPrefix.actual_entropy_preserved` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3EntropyPrefix.candidate_history_preserved` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3EntropyPrefix.entropy_words_joint` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Law.law_card` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Law.conditional_relabel` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Law.conditional_test` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Pair.fibre_product` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Pair.pair_fibres` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Pair.pair_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Pair.pair_joint_law` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Recorded.scalar_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Recorded.source_scalar_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Recorded.collect_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Recorded.qm31_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Schedule.scalar_control` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Schedule.scalar_permute` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Schedule.tower_permute` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Schedule.tower_refills` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SeedObstruction.raw_good` | `propext` |
| `R1Z.PV_L2_F3SeedObstruction.first_zero` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3SeedObstruction.first_one` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3SeedObstruction.lifted_position_changes` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SeedObstruction.old_l1_still_equal` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SourceArrays.initial_model` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SourceArrays.splitList_values` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SourceArrays.source_arrays` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SourceBudget.source_pair` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SourceBudget.masking` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SourceBudget.entropy` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SourceCounts.counted_no_values` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3SourceCounts.counted_list_step` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3SourceCounts.source_model` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SourceJoint.source_observed` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3SourceJoint.source_owned` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Tape.outputEquiv` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Tape.quotient_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Tape.owned_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Tape.observed_fibres` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Tape.owned_joint_law` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3WordCarrier.splitWord` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3WordCarrier.split_permute` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3WordCarrier.high_bit_preserved` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3WordCarrier.rejection_preserved` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3WordCarrier.accepted_permute` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3WordStream.splitStream` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3WordStream.split_stream_permute` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3WordStream.high_bits_preserved` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3WordStream.rejection_history_preserved` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3WordStream.actual_word_uniform` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Words.cellEquiv` | `propext, Quot.sound` |
| `R1Z.PV_L2_F3Words.accepts_permute` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F3Words.control_permute` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5.instrumented_erases` | `propext, Quot.sound` |
| `R1Z.PV_L2_F5.history_prefix` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5Absorption.fixed_coins_joint` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5Machine.execute_erases` | `propext, Quot.sound` |
| `R1Z.PV_L2_F5Machine.execute_history` | `propext, Quot.sound` |
| `R1Z.PV_L2_F5Machine.comparisons_bounded` | `propext, Quot.sound` |
| `R1Z.PV_L2_F5Machine.source_loop_record` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5Transport.real_to_lazy` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5Transport.lazy_to_middle` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F5Transport.completion_joint` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Dot.loop_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Dot.dot_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6DotStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6DotStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6DotStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Image.loop_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Image.image_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ImageStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ImageStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ImageStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6KDot.loop_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6KDot.kdot_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6KDotStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6KDotStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6KDotStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Openings.opens_queries` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Openings.parser_prefix_opens` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Openings.parser_queries` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Pivot.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Pivot.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Pivot.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Pivot.loop_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Pivot.piv_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Product.loop_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Product.product_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ProductOuterStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ProductOuterStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ProductOuterStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ProductRow.loop_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ProductRow.row_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ProductStep.recorded_erases` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ProductStep.unroll` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6ProductStep.increment` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Sharing.cursor_joint` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Sharing.singleton_layer` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Sharing.singleton_count` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Sharing.request_depths` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_F6Sharing.payload_erasure` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_Headline.deployed_parser` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_Headline.deployed_source_carrier` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_Headline.real_to_lazy_actual` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_Headline.absorption_actual` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_HeadlineF3.absorption_actual` | `propext, Classical.choice, Quot.sound` |
| `R1Z.PV_L2_Record.operation_bind_value` | `[]` |
| `R1Z.PV_L2_Record.pure_value` | `[]` |
| `R1Z.PV_L2_Record.bind_value` | `[]` |
| `R1Z.PV_L2_Record.operation_value` | `[]` |
| `R1Z.PV_L2_Record.fail_prefix` | `[]` |
| `R1Z.PV_L2_Record.div_prefix` | `[]` |
| `R1Z.PV_L2_RecordBind.erase_bind` | `[]` |
