-- Single frozen own-module import/axioms manifest; not a repository-wide
-- dependency replay, native equivalence certificate or privacy headline.
import R1Z.PV_CBL_ArrayCopied
import R1Z.PV_CBL_ArrayDeterminism
import R1Z.PV_CBL_ArrayExt
import R1Z.PV_CBL_ArrayFailure
import R1Z.PV_CBL_ArrayGuard
import R1Z.PV_CBL_ArrayImage
import R1Z.PV_CBL_ArrayKernel
import R1Z.PV_CBL_ArrayPrefix
import R1Z.PV_CBL_ArrayQM31
import R1Z.PV_CBL_ArrayReferenceTotal
import R1Z.PV_CBL_ArrayResult
import R1Z.PV_CBL_ArrayResultCases
import R1Z.PV_CBL_ArraySelection
import R1Z.PV_CBL_ArraySelectionFrame
import R1Z.PV_CBL_ArrayStep
import R1Z.PV_CBL_ArraySuccess
import R1Z.PV_CBL_ArrayTotal
import R1Z.PV_CBL_ArrayUnfold
import R1Z.PV_CBL_BufferInvariants
import R1Z.PV_CBL_BufferReference
import R1Z.PV_CBL_BundleFrame
import R1Z.PV_CBL_CallbackAudit
import R1Z.PV_CBL_CallbackBundle
import R1Z.PV_CBL_CarrierCoherence
import R1Z.PV_CBL_GenericArrayFlatten
import R1Z.PV_CBL_GenericArrayPower
import R1Z.PV_CBL_GenericArraySizes
import R1Z.PV_CBL_LibraryAPI
import R1Z.PV_CBL_LibraryShapeFrame
import R1Z.PV_CBL_LibraryShapeTypes
import R1Z.PV_CBL_LibraryShapes
import R1Z.PV_CBL_Op208Extracted
import R1Z.PV_CBL_Op208FailureFacts
import R1Z.PV_CBL_Op208Outcomes
import R1Z.PV_CBL_Op208Shape
import R1Z.PV_CBL_Op208SuccessFacts
import R1Z.PV_CBL_Op34Reference
import R1Z.PV_CBL_Op34Source
import R1Z.PV_CBL_Op34Transport
import R1Z.PV_CBL_Op35Reference
import R1Z.PV_CBL_Op35Source
import R1Z.PV_CBL_PathBorrowSource
import R1Z.PV_CBL_PathBytesReference
import R1Z.PV_CBL_PathJoinChecked
import R1Z.PV_CBL_PathJoinLength
import R1Z.PV_CBL_PathJoinShape
import R1Z.PV_CBL_PathJoinSuffix
import R1Z.PV_CBL_PathJoinValue
import R1Z.PV_CBL_PathOwnedReference
import R1Z.PV_CBL_PathTypeFrame
import R1Z.PV_CBL_PathTypes
import R1Z.PV_CBL_SelectionAudit
import R1Z.PV_CBL_SelectionFrame
import R1Z.PV_CBL_ShaBitLength
import R1Z.PV_CBL_ShaCore
import R1Z.PV_CBL_ShaCount
import R1Z.PV_CBL_ShaCountComposition
import R1Z.PV_CBL_ShaTypes
import R1Z.PV_CBL_SplitArithmetic
import R1Z.PV_CBL_SplitBounds
import R1Z.PV_CBL_SplitModel
import R1Z.PV_CBL_SplitRecompose
import R1Z.PV_CBL_StringAPI
import R1Z.PV_CBL_VectorPopReconstruct
import R1Z.PV_CBL_VectorPopSpec
import R1Z.PV_CBL_VectorReferenceFacts
import R1Z.PV_CBL_VectorShape
import R1Z.PV_CBL_WordReference
import R1Z.PV_CBL_WordReferenceIdentity
import R1Z.PV_CBL_WrapperFailure
import R1Z.PV_CBL_WrapperOutcomes
import R1Z.PV_CBL_WrapperReference
import R1Z.PV_CBL_WrapperSuccess

#print axioms PV_CBL_ArrayKernel.array_reference
#print axioms PV_CBL_ArrayKernel.array_reference_loop
#print axioms PV_CBL_ArrayKernel.array_reference_loop.body
#print axioms PV_CBL_Op34Reference.empty_reference
#print axioms PV_CBL_Op35Reference.default_reference
#print axioms PV_CBL_PathBytesReference.path_bytes_reference
#print axioms PV_CBL_PathOwnedReference.path_owned_reference
#print axioms PV_CBL_ShaCore.Core
#print axioms R1Z.PV_CBL_ArrayCopied.total_copied
#print axioms R1Z.PV_CBL_ArrayDeterminism.zero_independent
#print axioms R1Z.PV_CBL_ArrayExt.copied_unique
#print axioms R1Z.PV_CBL_ArrayFailure.body_oob
#print axioms R1Z.PV_CBL_ArrayFailure.read_oob
#print axioms R1Z.PV_CBL_ArrayGuard.correct_length
#print axioms R1Z.PV_CBL_ArrayGuard.wrong_length
#print axioms R1Z.PV_CBL_ArrayImage.finish
#print axioms R1Z.PV_CBL_ArrayImage.length
#print axioms R1Z.PV_CBL_ArrayImage.start
#print axioms R1Z.PV_CBL_ArrayImage.write_head
#print axioms R1Z.PV_CBL_ArrayPrefix.advance
#print axioms R1Z.PV_CBL_ArrayPrefix.copied
#print axioms R1Z.PV_CBL_ArrayPrefix.initial
#print axioms R1Z.PV_CBL_ArrayPrefix.set_get
#print axioms R1Z.PV_CBL_ArrayQM31.marker
#print axioms R1Z.PV_CBL_ArrayQM31.marker_irrelevant
#print axioms R1Z.PV_CBL_ArrayQM31.reference
#print axioms R1Z.PV_CBL_ArrayQM31.reject
#print axioms R1Z.PV_CBL_ArrayQM31.success
#print axioms R1Z.PV_CBL_ArrayQM31.zero
#print axioms R1Z.PV_CBL_ArrayReferenceTotal.none_iff
#print axioms R1Z.PV_CBL_ArrayReferenceTotal.total
#print axioms R1Z.PV_CBL_ArrayResult.reference
#print axioms R1Z.PV_CBL_ArrayResult.reject
#print axioms R1Z.PV_CBL_ArrayResult.success
#print axioms R1Z.PV_CBL_ArrayResultCases.complete
#print axioms R1Z.PV_CBL_ArraySelection.specialized_shape
#print axioms R1Z.PV_CBL_ArraySelection.transport
#print axioms R1Z.PV_CBL_ArraySelectionFrame.other_type
#print axioms R1Z.PV_CBL_ArraySelectionFrame.pop
#print axioms R1Z.PV_CBL_ArraySelectionFrame.reserve
#print axioms R1Z.PV_CBL_ArrayStep.continuing
#print axioms R1Z.PV_CBL_ArrayStep.done
#print axioms R1Z.PV_CBL_ArrayStep.increment
#print axioms R1Z.PV_CBL_ArrayStep.read
#print axioms R1Z.PV_CBL_ArrayStep.write
#print axioms R1Z.PV_CBL_ArraySuccess.success
#print axioms R1Z.PV_CBL_ArrayTotal.total
#print axioms R1Z.PV_CBL_ArrayUnfold.bind
#print axioms R1Z.PV_CBL_ArrayUnfold.unfold_loop
#print axioms R1Z.PV_CBL_BufferInvariants.eager
#print axioms R1Z.PV_CBL_BufferInvariants.eager_implies_lazy
#print axioms R1Z.PV_CBL_BufferInvariants.initial_eager
#print axioms R1Z.PV_CBL_BufferInvariants.initial_lazy
#print axioms R1Z.PV_CBL_BufferInvariants.lazy
#print axioms R1Z.PV_CBL_BufferReference.data
#print axioms R1Z.PV_CBL_BufferReference.data_length
#print axioms R1Z.PV_CBL_BufferReference.initial
#print axioms R1Z.PV_CBL_BufferReference.initial_data
#print axioms R1Z.PV_CBL_BufferReference.initial_pos
#print axioms R1Z.PV_CBL_BundleFrame.array
#print axioms R1Z.PV_CBL_BundleFrame.join
#print axioms R1Z.PV_CBL_BundleFrame.pop
#print axioms R1Z.PV_CBL_BundleFrame.reserve
#print axioms R1Z.PV_CBL_BundleFrame.sha_update
#print axioms R1Z.PV_CBL_CallbackAudit.supplied_family
#print axioms R1Z.PV_CBL_CallbackBundle.op25_source
#print axioms R1Z.PV_CBL_CallbackBundle.op29_source
#print axioms R1Z.PV_CBL_CallbackBundle.op34_source
#print axioms R1Z.PV_CBL_CallbackBundle.op34_source_all
#print axioms R1Z.PV_CBL_CallbackBundle.op35_source
#print axioms R1Z.PV_CBL_CallbackBundle.op35_source_all
#print axioms R1Z.PV_CBL_CarrierCoherence.blocks_path_unchanged
#print axioms R1Z.PV_CBL_CarrierCoherence.path_sha_commute
#print axioms R1Z.PV_CBL_CarrierCoherence.pathbuf_sha_unchanged
#print axioms R1Z.PV_CBL_GenericArrayFlatten.even
#print axioms R1Z.PV_CBL_GenericArrayFlatten.even_length
#print axioms R1Z.PV_CBL_GenericArrayFlatten.odd
#print axioms R1Z.PV_CBL_GenericArrayFlatten.odd_length
#print axioms R1Z.PV_CBL_GenericArrayPower.Storage
#print axioms R1Z.PV_CBL_GenericArrayPower.flatten
#print axioms R1Z.PV_CBL_GenericArrayPower.length
#print axioms R1Z.PV_CBL_GenericArraySizes.sha_block
#print axioms R1Z.PV_CBL_GenericArraySizes.sha_output
#print axioms R1Z.PV_CBL_LibraryShapeFrame.idempotent
#print axioms R1Z.PV_CBL_LibraryShapeFrame.path_commutes
#print axioms R1Z.PV_CBL_LibraryShapeFrame.sha_commutes
#print axioms R1Z.PV_CBL_LibraryShapeTypes.array_carrier
#print axioms R1Z.PV_CBL_LibraryShapeTypes.buffer_carrier
#print axioms R1Z.PV_CBL_LibraryShapes.Buffer
#print axioms R1Z.PV_CBL_LibraryShapes.CtWrapper
#print axioms R1Z.PV_CBL_LibraryShapes.Even
#print axioms R1Z.PV_CBL_LibraryShapes.GenericArray
#print axioms R1Z.PV_CBL_LibraryShapes.Odd
#print axioms R1Z.PV_CBL_LibraryShapes.Wrapper
#print axioms R1Z.PV_CBL_Op208Extracted.update_blocks
#print axioms R1Z.PV_CBL_Op208FailureFacts.divergence_iff
#print axioms R1Z.PV_CBL_Op208FailureFacts.failure_iff
#print axioms R1Z.PV_CBL_Op208Outcomes.full_result
#print axioms R1Z.PV_CBL_Op208Shape.extracted_shape
#print axioms R1Z.PV_CBL_Op208SuccessFacts.success_iff
#print axioms R1Z.PV_CBL_Op34Source.op34_source
#print axioms R1Z.PV_CBL_Op34Transport.reference_eq
#print axioms R1Z.PV_CBL_Op35Source.default_empty
#print axioms R1Z.PV_CBL_Op35Source.op34_preserved
#print axioms R1Z.PV_CBL_Op35Source.op35_source
#print axioms R1Z.PV_CBL_PathBorrowSource.op25_source
#print axioms R1Z.PV_CBL_PathBorrowSource.op29_source
#print axioms R1Z.PV_CBL_PathJoinChecked.reference
#print axioms R1Z.PV_CBL_PathJoinLength.bound
#print axioms R1Z.PV_CBL_PathJoinLength.length
#print axioms R1Z.PV_CBL_PathJoinLength.separator_bound
#print axioms R1Z.PV_CBL_PathJoinShape.absolute
#print axioms R1Z.PV_CBL_PathJoinShape.empty_base
#print axioms R1Z.PV_CBL_PathJoinShape.relative
#print axioms R1Z.PV_CBL_PathJoinShape.trailing_slash
#print axioms R1Z.PV_CBL_PathJoinSuffix.suffix
#print axioms R1Z.PV_CBL_PathJoinValue.join
#print axioms R1Z.PV_CBL_PathJoinValue.separator
#print axioms R1Z.PV_CBL_PathJoinValue.slash
#print axioms R1Z.PV_CBL_PathTypeFrame.block_buffer_unchanged
#print axioms R1Z.PV_CBL_PathTypeFrame.core_wrapper_unchanged
#print axioms R1Z.PV_CBL_PathTypeFrame.generic_array_unchanged
#print axioms R1Z.PV_CBL_PathTypeFrame.sha_core_unchanged
#print axioms R1Z.PV_CBL_PathTypeFrame.variable_wrapper_unchanged
#print axioms R1Z.PV_CBL_PathTypes.path_carrier
#print axioms R1Z.PV_CBL_PathTypes.pathbuf_carrier
#print axioms R1Z.PV_CBL_SelectionAudit.all_idempotent
#print axioms R1Z.PV_CBL_SelectionAudit.idempotent
#print axioms R1Z.PV_CBL_SelectionFrame.op25_preserved
#print axioms R1Z.PV_CBL_SelectionFrame.op26_preserved
#print axioms R1Z.PV_CBL_SelectionFrame.op28_preserved
#print axioms R1Z.PV_CBL_SelectionFrame.op29_preserved
#print axioms R1Z.PV_CBL_ShaBitLength.bitLength
#print axioms R1Z.PV_CBL_ShaBitLength.value
#print axioms R1Z.PV_CBL_ShaCount.cast_count
#print axioms R1Z.PV_CBL_ShaCount.wrapping_count
#print axioms R1Z.PV_CBL_ShaCount.zero_count
#print axioms R1Z.PV_CBL_ShaCountComposition.commute
#print axioms R1Z.PV_CBL_ShaCountComposition.twice
#print axioms R1Z.PV_CBL_ShaTypes.blocks_carrier
#print axioms R1Z.PV_CBL_ShaTypes.core_carrier
#print axioms R1Z.PV_CBL_SplitArithmetic.block_count_step
#print axioms R1Z.PV_CBL_SplitArithmetic.exact_blocks
#print axioms R1Z.PV_CBL_SplitArithmetic.exact_tail
#print axioms R1Z.PV_CBL_SplitArithmetic.no_blocks
#print axioms R1Z.PV_CBL_SplitArithmetic.tail_lt
#print axioms R1Z.PV_CBL_SplitBounds.block_index
#print axioms R1Z.PV_CBL_SplitBounds.consumed_and_tail
#print axioms R1Z.PV_CBL_SplitBounds.prefix_bound
#print axioms R1Z.PV_CBL_SplitBounds.tail_index
#print axioms R1Z.PV_CBL_SplitModel.block
#print axioms R1Z.PV_CBL_SplitModel.block_length
#print axioms R1Z.PV_CBL_SplitModel.tail
#print axioms R1Z.PV_CBL_SplitModel.tail_length
#print axioms R1Z.PV_CBL_SplitModel.zero_size_tail
#print axioms R1Z.PV_CBL_SplitRecompose.one
#print axioms R1Z.PV_CBL_SplitRecompose.prefix_tail
#print axioms R1Z.PV_CBL_VectorPopReconstruct.list
#print axioms R1Z.PV_CBL_VectorPopReconstruct.vector
#print axioms R1Z.PV_CBL_VectorPopSpec.length
#print axioms R1Z.PV_CBL_VectorPopSpec.pop
#print axioms R1Z.PV_CBL_VectorPopSpec.reference
#print axioms R1Z.PV_CBL_VectorPopSpec.total
#print axioms R1Z.PV_CBL_VectorReferenceFacts.default_len_zero
#print axioms R1Z.PV_CBL_VectorReferenceFacts.empty_divergence_impossible
#print axioms R1Z.PV_CBL_VectorReferenceFacts.empty_failure_impossible
#print axioms R1Z.PV_CBL_VectorReferenceFacts.empty_new
#print axioms R1Z.PV_CBL_VectorShape.emptyReference_eq
#print axioms R1Z.PV_CBL_WordReference.copyItem
#print axioms R1Z.PV_CBL_WordReference.copyItems
#print axioms R1Z.PV_CBL_WordReference.copyQ
#print axioms R1Z.PV_CBL_WordReference.copyWord
#print axioms R1Z.PV_CBL_WordReferenceIdentity.item
#print axioms R1Z.PV_CBL_WordReferenceIdentity.items
#print axioms R1Z.PV_CBL_WordReferenceIdentity.q
#print axioms R1Z.PV_CBL_WordReferenceIdentity.word
#print axioms R1Z.PV_CBL_WrapperFailure.buffer_failure
#print axioms R1Z.PV_CBL_WrapperFailure.core_divergence
#print axioms R1Z.PV_CBL_WrapperFailure.core_failure
#print axioms R1Z.PV_CBL_WrapperOutcomes.default_full_result
#print axioms R1Z.PV_CBL_WrapperOutcomes.finalize_full_result
#print axioms R1Z.PV_CBL_WrapperReference.finalize
#print axioms R1Z.PV_CBL_WrapperReference.makeDefault
#print axioms R1Z.PV_CBL_WrapperSuccess.default_iff
#print axioms R1Z.PV_CBL_WrapperSuccess.finalize_iff
