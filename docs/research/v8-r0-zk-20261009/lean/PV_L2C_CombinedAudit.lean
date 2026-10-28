import PV_L2C_HonestCaller
import PV_L2C_HonestHelper
import PV_L2C_HonestValidity
import PV_L2C_HonestSumcheck
import PV_L2C_VecBack
import PV_L2C_OwnedBalance
import PV_L2C_RowEnumeration
import PV_L2C_SelectedDense
import PV_L2C_ExtractedGuard
import PV_L2C_ParserSlices
import PV_L2C_ComplexParser
import PV_L2C_ParserHalves8
import PV_L2C_QParser
import PV_L2C_ScalarBalance
import PV_L2C_ScalarCanonical
import PV_L2C_CanonicalityBoundary
import R1Z.PV_RunJoin_ConsumerBoundary25
import PV_L2C_VecShape
import PV_L2C_PackedMasks
import PV_L2C_ExtractedM31Fold
import PV_L2C_ExtractedRows
import PV_L2C_VecWrite
import PV_L2C_PaddingProducer
import PV_L2C_PaddingConsumer
import PV_L2C_M31
import PV_L2C_NativeFold
import PV_L2C_NativeBalance
import PV_L2C_NativeQ
import PV_L2C_QBalance
import PV_L2C_Reducer
import PV_L2C_SampleCanonical
import PV_L2C_CanonicalParser
import PV_L2C_QFold
import PV_L2C_PaddingNative
import PV_L2C_SparseFold
import PV_L2C_ReferenceArithmetic
import PV_L2C_SubPrimitive
import PV_L2C_NormalizeSource
import PV_L2C_ReferenceSub
import PV_L2C_ReferenceQ
import PV_L2C_FirstInactive
import PV_L2C_VecRead
import PV_L2C_ExtractedFold

/-! Combined local-laws audit. No native HonestInput guard refinement is asserted. -/
#print axioms PV_L2C_PaddingProducer.sampled_active
#print axioms PV_L2C_PaddingProducer.balanced_active
#print axioms PV_L2C_PaddingProducer.balanced_sum
#print axioms PV_L2C_PaddingProducer.padding_guards
#print axioms PV_L2C_PaddingConsumer.active_branch
#print axioms PV_L2C_PaddingConsumer.sum_branch
#print axioms PV_L2C_PaddingConsumer.scan_false
#print axioms PV_L2C_PaddingConsumer.all_active_branches
#print axioms PV_L2C_M31.subtractP_branch
#print axioms PV_L2C_M31.subtractP_nat
#print axioms PV_L2C_M31.subtractP_canonical
#print axioms PV_L2C_M31.add_nat
#print axioms PV_L2C_M31.add_canonical
#print axioms PV_L2C_M31.add_decode
#print axioms PV_L2C_M31.subtractP_decode
#print axioms PV_L2C_M31.sub_input_nat
#print axioms PV_L2C_M31.sub_canonical
#print axioms PV_L2C_M31.sub_decode
#print axioms PV_L2C_M31.decode_injective
#print axioms PV_L2C_M31.zero_guard
#print axioms PV_L2C_NativeFold.fold_canonical
#print axioms PV_L2C_NativeFold.fold_decode
#print axioms PV_L2C_NativeFold.fold_zero_decode
#print axioms PV_L2C_NativeFold.negate_decode
#print axioms PV_L2C_NativeBalance.rebalance_canonical
#print axioms PV_L2C_NativeBalance.rebalance_decode_sum
#print axioms PV_L2C_NativeBalance.audit_zero
#print axioms PV_L2C_NativeBalance.audit_branch
#print axioms PV_L2C_NativeQ.zero_canonical
#print axioms PV_L2C_NativeQ.add_canonical
#print axioms PV_L2C_NativeQ.sub_canonical
#print axioms PV_L2C_NativeQ.add_decode
#print axioms PV_L2C_NativeQ.sub_decode
#print axioms PV_L2C_NativeQ.decode_injective
#print axioms PV_L2C_NativeQ.zero_decode
#print axioms PV_L2C_NativeQ.zero_guard
#print axioms PV_L2C_QBalance.fold_component
#print axioms PV_L2C_QBalance.rebalance_component
#print axioms PV_L2C_QBalance.rebalance_audit
#print axioms PV_L2C_QBalance.rebalance_branch
#print axioms PV_L2C_Reducer.first_bound
#print axioms PV_L2C_Reducer.second_bound
#print axioms PV_L2C_Reducer.fold_decode
#print axioms PV_L2C_Reducer.reduction_bound
#print axioms PV_L2C_SampleCanonical.scalar_canonical
#print axioms PV_L2C_SampleCanonical.tuple_canonical
#print axioms PV_L2C_SampleCanonical.secure_canonical
#print axioms PV_L2C_CanonicalParser.word_roundtrip
#print axioms PV_L2C_CanonicalParser.scalar_parse
#print axioms PV_L2C_QFold.canonical_fold
#print axioms PV_L2C_QFold.decode_fold
#print axioms PV_L2C_QFold.tableSum_canonical
#print axioms PV_L2C_QFold.tableSum_decode
#print axioms PV_L2C_QFold.inactive_canonical
#print axioms PV_L2C_QFold.inactive_decode
#print axioms PV_L2C_QFold.native_add_zero
#print axioms PV_L2C_PaddingNative.without_canonical
#print axioms PV_L2C_PaddingNative.excluded_canonical
#print axioms PV_L2C_PaddingNative.rebalance_canonical
#print axioms PV_L2C_PaddingNative.excluded_decode
#print axioms PV_L2C_PaddingNative.rebalance_decode
#print axioms PV_L2C_PaddingNative.raw_sum_zero
#print axioms PV_L2C_PaddingNative.sample_canonical
#print axioms PV_L2C_PaddingNative.active_zero
#print axioms PV_L2C_PaddingNative.guard_outcomes
#print axioms PV_L2C_SparseFold.dense_projection
#print axioms PV_L2C_SparseFold.source_sum
#print axioms PV_L2C_ReferenceArithmetic.m31_add
#print axioms PV_L2C_SubPrimitive.wrapped_sub
#print axioms PV_L2C_SubPrimitive.wrapped_add
#print axioms PV_L2C_NormalizeSource.wrap_eta
#print axioms PV_L2C_NormalizeSource.modulus
#print axioms PV_L2C_NormalizeSource.normalize_native
#print axioms PV_L2C_NormalizeSource.sub_input
#print axioms PV_L2C_NormalizeSource.sub_cut
#print axioms PV_L2C_ReferenceSub.m31_sub
#print axioms PV_L2C_ReferenceQ.source_roundtrip
#print axioms PV_L2C_ReferenceQ.model_roundtrip
#print axioms PV_L2C_ReferenceQ.source_zero
#print axioms PV_L2C_ReferenceQ.add_source
#print axioms PV_L2C_ReferenceQ.sub_source
#print axioms PV_L2C_ReferenceQ.add_actual
#print axioms PV_L2C_ReferenceQ.sub_actual
#print axioms PV_L2C_FirstInactive.returned
#print axioms PV_L2C_FirstInactive.table_returned
#print axioms PV_L2C_VecRead.bound1024
#print axioms PV_L2C_VecRead.read
#print axioms PV_L2C_VecRead.read_active
#print axioms PV_L2C_ExtractedFold.source
#print axioms PV_L2C_ExtractedFold.canonical_sum
#print axioms PV_L2C_ExtractedFold.zero_sum
#print axioms PV_L2C_VecWrite.index_mut
#print axioms PV_L2C_VecWrite.write
#print axioms PV_L2C_ExtractedRows.row_source
#print axioms PV_L2C_ExtractedRows.read_step
#print axioms PV_L2C_ExtractedRows.fold_source
#print axioms PV_L2C_ExtractedM31Fold.source
#print axioms PV_L2C_ExtractedM31Fold.zero_sum
#print axioms PV_L2C_PackedMasks.inserted_bit
#print axioms PV_L2C_PackedMasks.put_contains
#print axioms PV_L2C_PackedMasks.packed_contains
#print axioms PV_L2C_VecShape.length
#print axioms PV_L2C_VecShape.active_read


/-! D355 continuation: complete Results and exact-carrier decoded facts.
No universal native HonestInput guard claim is imported or asserted. -/
#print axioms PV_L2C_HonestCaller.identification
#print axioms PV_L2C_HonestCaller.returned_bank
#print axioms PV_L2C_HonestCaller.builder_sound
#print axioms PV_L2C_HonestHelper.total
#print axioms PV_L2C_HonestHelper.inactive
#print axioms PV_L2C_HonestValidity.valid
#print axioms PV_L2C_HonestSumcheck.initial
#print axioms PV_L2C_HonestSumcheck.chain
#print axioms PV_L2C_HonestSumcheck.terminal
#print axioms PV_L2C_VecBack.index_mut
#print axioms PV_L2C_VecBack.write
#print axioms PV_L2C_OwnedBalance.complete_result
#print axioms PV_L2C_RowEnumeration.enumeration
#print axioms PV_L2C_SelectedDense.selected_sum
#print axioms PV_L2C_ExtractedGuard.padding_result
#print axioms PV_L2C_ComplexParser.parse
#print axioms PV_L2C_QParser.parse
#print axioms PV_L2C_ScalarBalance.complete_result
#print axioms PV_L2C_ScalarCanonical.output_canonical
#print axioms PV_L2C_CanonicalityBoundary.decoded_equality_insufficient
