import R1Z.ProverCommitBasisPolynomial48
import R1Z.ProverCommitBatchMix48
import R1Z.ProverCommitCounterList48
import R1Z.ProverCommitDualCell48
import R1Z.ProverCommitExtra48
import R1Z.ProverCommitFoldCell48
import R1Z.ProverCommitFoldOutput48
import R1Z.ProverCommitFoldRange48
import R1Z.ProverCommitFoldValue48
import R1Z.ProverCommitGamma48
import R1Z.ProverCommitInterpolationAccumulate48
import R1Z.ProverCommitInterpolationBasis48
import R1Z.ProverCommitInterpolationBytes48
import R1Z.ProverCommitInterpolationEmbed48
import R1Z.ProverCommitInterpolationFactors48
import R1Z.ProverCommitInterpolationIndices48
import R1Z.ProverCommitInterpolationInitial48
import R1Z.ProverCommitInterpolationInverse48
import R1Z.ProverCommitInterpolationModel48
import R1Z.ProverCommitInterpolationOutput48
import R1Z.ProverCommitInterpolationPoly48
import R1Z.ProverCommitInterpolationRow48
import R1Z.ProverCommitInterpolationSchedule48
import R1Z.ProverCommitInverse48
import R1Z.ProverCommitIteratorConsumer48
import R1Z.ProverCommitIteratorStd48
import R1Z.ProverCommitLagrangeProduct48
import R1Z.ProverCommitM31Array48
import R1Z.ProverCommitM31Ops48
import R1Z.ProverCommitMix48
import R1Z.ProverCommitMulU48
import R1Z.ProverCommitNativeEval48
import R1Z.ProverCommitNativePair48
import R1Z.ProverCommitNativeQ48
import R1Z.ProverCommitPowers48
import R1Z.ProverCommitQArray48
import R1Z.ProverCommitQOps48
import R1Z.ProverCommitQuarter48
import R1Z.ProverCommitRoundLoop48
import R1Z.ProverCommitRoundOutput48
import R1Z.ProverCommitRoundScaled48
import R1Z.ProverCommitRoundStep48
import R1Z.ProverCommitScalar48
import R1Z.ProverCommitWideArray48
import R1Z.ProverCommitWideBytes48
import R1Z.ProverCommitWideOps48
import R1Z.ProverCommitWideScalar48
import R1Z.ProverCommitY1Aggregate48
import R1Z.ProverCommitDeployedFuel22

/-! Final focused audit of part 48 accepted theorem declarations.
This is not a complete frozen manifest replay or a simulator refinement claim. -/
#print axioms R1Z.ProverCommitBasisPolynomial48.multiplication
#print axioms R1Z.ProverCommitBatchMix48.sum_powers
#print axioms R1Z.ProverCommitBatchMix48.value_exact
#print axioms R1Z.ProverCommitCounterList48.increment
#print axioms R1Z.ProverCommitCounterList48.bounds
#print axioms R1Z.ProverCommitCounterList48.values
#print axioms R1Z.ProverCommitDualCell48.cell
#print axioms R1Z.ProverCommitExtra48.index
#print axioms R1Z.ProverCommitExtra48.horner_value
#print axioms R1Z.ProverCommitExtra48.source_zero
#print axioms R1Z.ProverCommitExtra48.extra_value
#print axioms R1Z.ProverCommitFoldCell48.cell
#print axioms R1Z.ProverCommitFoldOutput48.first_exact
#print axioms R1Z.ProverCommitFoldOutput48.second_exact
#print axioms R1Z.ProverCommitFoldOutput48.run_image
#print axioms R1Z.ProverCommitFoldOutput48.fin_bytes
#print axioms R1Z.ProverCommitFoldRange48.first_source
#print axioms R1Z.ProverCommitFoldRange48.second_source
#print axioms R1Z.ProverCommitFoldRange48.four_val
#print axioms R1Z.ProverCommitFoldRange48.offset_val
#print axioms R1Z.ProverCommitFoldRange48.four_array
#print axioms R1Z.ProverCommitFoldValue48.range_value
#print axioms R1Z.ProverCommitGamma48.zero_canonical
#print axioms R1Z.ProverCommitGamma48.one_canonical
#print axioms R1Z.ProverCommitGamma48.zero_value
#print axioms R1Z.ProverCommitGamma48.one_value
#print axioms R1Z.ProverCommitGamma48.source_zero
#print axioms R1Z.ProverCommitGamma48.source_one
#print axioms R1Z.ProverCommitGamma48.repeat_zero
#print axioms R1Z.ProverCommitGamma48.gamma_exact
#print axioms R1Z.ProverCommitGamma48.kappa_exact
#print axioms R1Z.ProverCommitInterpolationAccumulate48.accumulate_value
#print axioms R1Z.ProverCommitInterpolationBasis48.basis_value
#print axioms R1Z.ProverCommitInterpolationBytes48.output_spec
#print axioms R1Z.ProverCommitInterpolationBytes48.coefficient
#print axioms R1Z.ProverCommitInterpolationBytes48.cell_image
#print axioms R1Z.ProverCommitInterpolationBytes48.encoded_image
#print axioms R1Z.ProverCommitInterpolationBytes48.byte_count
#print axioms R1Z.ProverCommitInterpolationEmbed48.source_embed
#print axioms R1Z.ProverCommitInterpolationFactors48.factors_value
#print axioms R1Z.ProverCommitInterpolationIndices48.size_u8
#print axioms R1Z.ProverCommitInterpolationIndices48.cast32_val
#print axioms R1Z.ProverCommitInterpolationIndices48.cast32_canonical
#print axioms R1Z.ProverCommitInterpolationIndices48.cast32_decode
#print axioms R1Z.ProverCommitInterpolationIndices48.add_val
#print axioms R1Z.ProverCommitInterpolationIndices48.next_val
#print axioms R1Z.ProverCommitInterpolationInitial48.initial_canonical
#print axioms R1Z.ProverCommitInterpolationInitial48.initial_value
#print axioms R1Z.ProverCommitInterpolationInitial48.initial_poly
#print axioms R1Z.ProverCommitInterpolationInitial48.initial_source
#print axioms R1Z.ProverCommitInterpolationInitial48.prepare_exact
#print axioms R1Z.ProverCommitInterpolationInverse48.square_counter
#print axioms R1Z.ProverCommitInterpolationInverse48.source_square
#print axioms R1Z.ProverCommitInterpolationInverse48.source_inverse
#print axioms R1Z.ProverCommitInterpolationInverse48.inverse_exact
#print axioms R1Z.ProverCommitInterpolationModel48.basis_map
#print axioms R1Z.ProverCommitInterpolationModel48.contribution_basis
#print axioms R1Z.ProverCommitInterpolationModel48.sum_range
#print axioms R1Z.ProverCommitInterpolationModel48.sum_model
#print axioms R1Z.ProverCommitInterpolationModel48.interpolate_model
#print axioms R1Z.ProverCommitInterpolationOutput48.step
#print axioms R1Z.ProverCommitInterpolationOutput48.rows_value
#print axioms R1Z.ProverCommitInterpolationOutput48.zero_poly
#print axioms R1Z.ProverCommitInterpolationOutput48.interpolate_value
#print axioms R1Z.ProverCommitInterpolationPoly48.coeff
#print axioms R1Z.ProverCommitInterpolationPoly48.mul_coeff
#print axioms R1Z.ProverCommitInterpolationPoly48.mul_shape
#print axioms R1Z.ProverCommitInterpolationRow48.row_value
#print axioms R1Z.ProverCommitInterpolationSchedule48.degree_le
#print axioms R1Z.ProverCommitInterpolationSchedule48.skipped_degree
#print axioms R1Z.ProverCommitInterpolationSchedule48.selected_degree
#print axioms R1Z.ProverCommitInterpolationSchedule48.selected_room
#print axioms R1Z.ProverCommitInterpolationSchedule48.self_eval
#print axioms R1Z.ProverCommitInterpolationSchedule48.nat_cast_ne
#print axioms R1Z.ProverCommitInterpolationSchedule48.denominator_nonzero
#print axioms R1Z.ProverCommitInverse48.multiply_word
#print axioms R1Z.ProverCommitInverse48.word_mul
#print axioms R1Z.ProverCommitInverse48.release_multiply
#print axioms R1Z.ProverCommitInverse48.square_decode
#print axioms R1Z.ProverCommitInverse48.power_step
#print axioms R1Z.ProverCommitInverse48.chain_exponent
#print axioms R1Z.ProverCommitInverse48.inverse_decode
#print axioms R1Z.ProverCommitInverse48.square_result
#print axioms R1Z.ProverCommitInverse48.inverse_result
#print axioms R1Z.ProverCommitInverse48.inverse_exact
#print axioms R1Z.ProverCommitInverse48.inverse_canonical
#print axioms R1Z.ProverCommitIteratorConsumer48.model_consistent
#print axioms R1Z.ProverCommitIteratorConsumer48.reverse_fold
#print axioms R1Z.ProverCommitIteratorConsumer48.encoded
#print axioms R1Z.ProverCommitIteratorStd48.model_consistent
#print axioms R1Z.ProverCommitIteratorStd48.pair_cursor
#print axioms R1Z.ProverCommitIteratorStd48.pair_count
#print axioms R1Z.ProverCommitLagrangeProduct48.normalized_product
#print axioms R1Z.ProverCommitLagrangeProduct48.normalized_basis
#print axioms R1Z.ProverCommitM31Array48.index
#print axioms R1Z.ProverCommitM31Array48.update
#print axioms R1Z.ProverCommitM31Array48.previous_val
#print axioms R1Z.ProverCommitM31Array48.predecessor_value
#print axioms R1Z.ProverCommitM31Ops48.mul_exact
#print axioms R1Z.ProverCommitM31Ops48.add_exact
#print axioms R1Z.ProverCommitM31Ops48.sub_exact
#print axioms R1Z.ProverCommitMix48.index
#print axioms R1Z.ProverCommitMix48.source_finite
#print axioms R1Z.ProverCommitMix48.finite_value
#print axioms R1Z.ProverCommitMix48.owner_value
#print axioms R1Z.ProverCommitMulU48.r_coordinates
#print axioms R1Z.ProverCommitMulU48.mul_u
#print axioms R1Z.ProverCommitNativeEval48.basis_owner
#print axioms R1Z.ProverCommitNativeEval48.run_owner
#print axioms R1Z.ProverCommitNativeEval48.raw_value
#print axioms R1Z.ProverCommitNativeEval48.bytes
#print axioms R1Z.ProverCommitNativePair48.range_finite
#print axioms R1Z.ProverCommitNativePair48.range_owner
#print axioms R1Z.ProverCommitNativePair48.evaluate_owner
#print axioms R1Z.ProverCommitNativeQ48.add
#print axioms R1Z.ProverCommitNativeQ48.mul
#print axioms R1Z.ProverCommitNativeQ48.sub
#print axioms R1Z.ProverCommitPowers48.set_source
#print axioms R1Z.ProverCommitPowers48.fill_value
#print axioms R1Z.ProverCommitQArray48.index
#print axioms R1Z.ProverCommitQArray48.update
#print axioms R1Z.ProverCommitQArray48.source_zero
#print axioms R1Z.ProverCommitQArray48.repeat_zero
#print axioms R1Z.ProverCommitQOps48.add
#print axioms R1Z.ProverCommitQOps48.mul
#print axioms R1Z.ProverCommitQOps48.r_raw
#print axioms R1Z.ProverCommitQuarter48.base_quarter
#print axioms R1Z.ProverCommitQuarter48.factor_quarter
#print axioms R1Z.ProverCommitRoundLoop48.loop_value
#print axioms R1Z.ProverCommitRoundOutput48.indices_legal
#print axioms R1Z.ProverCommitRoundOutput48.accumulation
#print axioms R1Z.ProverCommitRoundScaled48.scale_list
#print axioms R1Z.ProverCommitRoundScaled48.scaled_output
#print axioms R1Z.ProverCommitRoundStep48.permutation
#print axioms R1Z.ProverCommitRoundStep48.step
#print axioms R1Z.ProverCommitScalar48.word_canonical
#print axioms R1Z.ProverCommitScalar48.word_decode
#print axioms R1Z.ProverCommitScalar48.product_canonical
#print axioms R1Z.ProverCommitScalar48.product_value
#print axioms R1Z.ProverCommitScalar48.source_exact
#print axioms R1Z.ProverCommitWideArray48.update
#print axioms R1Z.ProverCommitWideBytes48.limbs_image
#print axioms R1Z.ProverCommitWideBytes48.source_image
#print axioms R1Z.ProverCommitWideBytes48.source_decode
#print axioms R1Z.ProverCommitWideOps48.checked_add
#print axioms R1Z.ProverCommitWideOps48.mul_coordinates
#print axioms R1Z.ProverCommitWideOps48.checked_mul
#print axioms R1Z.ProverCommitWideOps48.add_exact
#print axioms R1Z.ProverCommitWideOps48.mul_exact
#print axioms R1Z.ProverCommitWideScalar48.qm_scalar
#print axioms R1Z.ProverCommitWideScalar48.normalized_embed
#print axioms R1Z.ProverCommitWideScalar48.product_canonical
#print axioms R1Z.ProverCommitWideScalar48.product_value
#print axioms R1Z.ProverCommitWideScalar48.source_exact
#print axioms R1Z.ProverCommitY1Aggregate48.value_spec
#print axioms R1Z.ProverCommitY1Aggregate48.cell_image
#print axioms R1Z.ProverCommitY1Aggregate48.evaluations_exact
#print axioms R1Z.ProverCommitY1Aggregate48.encoded_image
#print axioms R1Z.ProverCommitY1Aggregate48.every_lane
#print axioms R1Z.ProverCommitY1Aggregate48.byte_count
#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed
