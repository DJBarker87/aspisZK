import R22FastPairingRawRanges
import R22ControlBounds
import R22DecodeValueTotal
import R22DecodeLoopTotal
import R22BatchedPushTotal
import R22BatchedValueTotal
import CheckedWrappingScalarAgreement
import R22CanonicalM31AddSub
import R22CurrentReducerMul
import R22CanonicalCM31
import R22CanonicalQM31
import R22FastPairingPrimitiveBounds

/-! One combined public-theorem axioms audit for this focused packet. -/
#print axioms AspisR1.R22FastPairingRawRanges.partial_le_three_p
#print axioms AspisR1.R22FastPairingRawRanges.raw_ranges
#print axioms AspisR1.R22ControlBounds.round_rows
#print axioms AspisR1.R22ControlBounds.prepare_rows
#print axioms AspisR1.R22ControlBounds.horner_indices
#print axioms AspisR1.R22ControlBounds.boundary_successor
#print axioms AspisR1.R22ControlBounds.fast_dot_offsets
#print axioms AspisR1.R22ControlBounds.fast_dot_tails
#print axioms AspisR1.R22ControlBounds.weights_digits
#print axioms AspisR1.R22ControlBounds.libra_indices
#print axioms AspisR1.R22ControlBounds.point_indices
#print axioms AspisR1.R22ControlBounds.sampler_word_indices
#print axioms AspisR1.R22ControlBounds.sampler_dividend
#print axioms AspisR1.R22DecodeValueTotal.size_guards
#print axioms AspisR1.R22DecodeValueTotal.decode_value_total
#print axioms AspisR1.R22DecodeLoopTotal.decode_loop_total
#print axioms AspisR1.R22BatchedPushTotal.push_total
#print axioms AspisR1.R22BatchedValueTotal.reducer_eq
#print axioms AspisR1.R22BatchedValueTotal.value_total
#print axioms AspisR1.CheckedWrappingScalarAgreement.add_success_agrees
#print axioms AspisR1.CheckedWrappingScalarAgreement.sub_success_agrees
#print axioms AspisR1.CheckedWrappingScalarAgreement.mul_success_agrees
#print axioms AspisR1.R22CanonicalM31AddSub.checkedFinish_eq
#print axioms AspisR1.R22CanonicalM31AddSub.canonical_add_agrees
#print axioms AspisR1.R22CanonicalM31AddSub.canonical_sub_agrees
#print axioms AspisR1.R22CanonicalM31AddSub.wrapping_add_canonical
#print axioms AspisR1.R22CanonicalM31AddSub.wrapping_sub_canonical
#print axioms AspisR1.R22CurrentReducerMul.fold_agrees
#print axioms AspisR1.R22CurrentReducerMul.reduce_agrees
#print axioms AspisR1.R22CurrentReducerMul.current_reducer_agrees
#print axioms AspisR1.R22CurrentReducerMul.current_mul_agrees
#print axioms AspisR1.R22CurrentReducerMul.wrapping_reduce_mod
#print axioms AspisR1.R22CurrentReducerMul.wrapping_mul_mod
#print axioms AspisR1.R22CanonicalCM31.cm_add_agrees
#print axioms AspisR1.R22CanonicalCM31.cm_sub_agrees
#print axioms AspisR1.R22CanonicalCM31.cm_add_canonical
#print axioms AspisR1.R22CanonicalCM31.cm_sub_canonical
#print axioms AspisR1.R22CanonicalCM31.cross_agrees
#print axioms AspisR1.R22CanonicalCM31.cm_mul_agrees
#print axioms AspisR1.R22CanonicalCM31.cm_mul_canonical
#print axioms AspisR1.R22CanonicalQM31.byR_agrees
#print axioms AspisR1.R22CanonicalQM31.byR_canonical
#print axioms AspisR1.R22CanonicalQM31.qm_add_agrees
#print axioms AspisR1.R22CanonicalQM31.qm_add_canonical
#print axioms AspisR1.R22CanonicalQM31.qm_mul_agrees
#print axioms AspisR1.R22CanonicalQM31.qm_mul_canonical
#print axioms AspisR1.R22FastPairingPrimitiveBounds.wrapping_fold_lt
#print axioms AspisR1.R22FastPairingPrimitiveBounds.folded_multiple_agrees
#print axioms AspisR1.R22FastPairingPrimitiveBounds.widened_product_agrees
#print axioms AspisR1.R22FastPairingPrimitiveBounds.constant_multiple_agrees
