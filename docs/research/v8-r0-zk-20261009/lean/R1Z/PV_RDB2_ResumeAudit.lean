import R1Z.PV_RDB2_230_Funs
import R1Z.PV_RDB2_230_Types
import R1Z.PV_RDB2_AL_BlockCodec
import R1Z.PV_RDB2_ActualCarrier230
import R1Z.PV_RDB2_Alignment
import R1Z.PV_RDB2_AppliedCarrier
import R1Z.PV_RDB2_Applied_00_P
import R1Z.PV_RDB2_Applied_01_ct_subtract_p
import R1Z.PV_RDB2_Applied_02_ct_reduce64
import R1Z.PV_RDB2_Applied_03_ct_add
import R1Z.PV_RDB2_Applied_04_ct_sub
import R1Z.PV_RDB2_Applied_05_M31_ZERO
import R1Z.PV_RDB2_Applied_06_reduce_u64
import R1Z.PV_RDB2_Applied_07_M31_mul
import R1Z.PV_RDB2_Applied_08_M31_reduce_u64
import R1Z.PV_RDB2_Applied_09_M31_add
import R1Z.PV_RDB2_Applied_10_M31_double
import R1Z.PV_RDB2_Applied_11_CM31_ZERO
import R1Z.PV_RDB2_Applied_12_CM31_from_m31
import R1Z.PV_RDB2_Applied_13_CM31_add
import R1Z.PV_RDB2_Applied_14_M31_sub
import R1Z.PV_RDB2_Applied_15_CM31_sub
import R1Z.PV_RDB2_Applied_16_CM31_mul
import R1Z.PV_RDB2_Applied_17_CM31_mul_m31
import R1Z.PV_RDB2_Applied_18_mul_by_r
import R1Z.PV_RDB2_Applied_19_QM31_from_cm31
import R1Z.PV_RDB2_Applied_20_QM31_add
import R1Z.PV_RDB2_Applied_21_QM31_mul
import R1Z.PV_RDB2_Applied_22_QM31_mul_m31
import R1Z.PV_RDB2_Applied_23_compress_loop_body
import R1Z.PV_RDB2_Applied_24_compress_loop
import R1Z.PV_RDB2_Applied_25_compress
import R1Z.PV_RDB2_Atomic
import R1Z.PV_RDB2_CBL_ArrayKernel
import R1Z.PV_RDB2_CBL_ArrayPrefix
import R1Z.PV_RDB2_CBL_GenericArrayFlatten
import R1Z.PV_RDB2_CBL_GenericArrayPower
import R1Z.PV_RDB2_CBL_LibraryShapeTypes
import R1Z.PV_RDB2_CBL_LibraryShapes
import R1Z.PV_RDB2_CBL_PadListFacts
import R1Z.PV_RDB2_CBL_PaddingModel
import R1Z.PV_RDB2_CBL_WrapperReference
import R1Z.PV_RDB2_Compress
import R1Z.PV_RDB2_ConstructorEffects
import R1Z.PV_RDB2_CopyEffects
import R1Z.PV_RDB2_CtCopy
import R1Z.PV_RDB2_DL_ArrayShape
import R1Z.PV_RDB2_DL_CtCarrier
import R1Z.PV_RDB2_DL_CtFinal
import R1Z.PV_RDB2_DL_CtSelected
import R1Z.PV_RDB2_DL_DefaultBuffer
import R1Z.PV_RDB2_DL_DefaultCallback
import R1Z.PV_RDB2_DL_DefaultSelected
import R1Z.PV_RDB2_DL_Forwarding
import R1Z.PV_RDB2_DL_StorageBuild
import R1Z.PV_RDB2_DL_Truncation
import R1Z.PV_RDB2_Fold
import R1Z.PV_RDB2_FullExternalFuns
import R1Z.PV_RDB2_FullExternalTypes
import R1Z.PV_RDB2_FullFuns
import R1Z.PV_RDB2_FullTypes
import R1Z.PV_RDB2_GlobalAlloc
import R1Z.PV_RDB2_Index
import R1Z.PV_RDB2_Layout
import R1Z.PV_RDB2_LayoutGeneral
import R1Z.PV_RDB2_LayoutGuards
import R1Z.PV_RDB2_LayoutPad
import R1Z.PV_RDB2_LayoutRepeat
import R1Z.PV_RDB2_Loop
import R1Z.PV_RDB2_MutBorrow
import R1Z.PV_RDB2_MutMixed
import R1Z.PV_RDB2_NonNull
import R1Z.PV_RDB2_P6CompressSource
import R1Z.PV_RDB2_Pointer
import R1Z.PV_RDB2_PointerBridge
import R1Z.PV_RDB2_RawVec
import R1Z.PV_RDB2_Realloc
import R1Z.PV_RDB2_ResultEffects
import R1Z.PV_RDB2_SumControl
import R1Z.PV_RDB2_SumDeployed
import R1Z.PV_RDB2_SumFold
import R1Z.PV_RDB2_SumNative
import R1Z.PV_RDB2_SumOriginal
import R1Z.PV_RDB2_Transport
import R1Z.PV_RDB2_Truncate
import R1Z.PV_RDB2_VecBorrow

/-! Combined audit of the final owned, import-narrowed cohort.
No endpoint or compiler-correspondence claim is made. -/
#print axioms PV_B1_230.TRACE_ROWS
#print axioms PV_B1_230.aspis_core.field.CM31
#print axioms PV_B1_230.aspis_core.field.CM31.add
#print axioms PV_B1_230.aspis_core.field.M31
#print axioms PV_B1_230.aspis_core.field.M31.add
#print axioms PV_B1_230.aspis_core.field.P
#print axioms PV_B1_230.aspis_core.field.QM31
#print axioms PV_B1_230.aspis_core.field.QM31.ZERO
#print axioms PV_B1_230.aspis_core.field.QM31.add
#print axioms PV_B1_230.aspis_core.field.ct.add
#print axioms PV_B1_230.aspis_core.field.ct.subtract_p
#print axioms PV_B1_230.state_only_copy_helper_sum
#print axioms PV_B1_230.state_only_copy_helper_sum_loop
#print axioms PV_B1_230.state_only_copy_helper_sum_loop.body
#print axioms PV_B1_ActualCarrier230.from_to
#print axioms PV_B1_ActualCarrier230.injective
#print axioms PV_B1_ActualCarrier230.to_from
#print axioms PV_B1_Loop.bind
#print axioms PV_B1_SumControl.dispatch_congr
#print axioms PV_B1_SumControl.loop_finite
#print axioms PV_B1_SumControl.op230_source
#print axioms PV_B1_SumControl.source_unfold
#print axioms PV_B1_SumFold.finite
#print axioms PV_B1_SumFold.op230_source
#print axioms PV_B1_SumFold.read
#print axioms PV_B1_SumFold.step
#print axioms PV_B1_SumNative.add_source
#print axioms PV_B1_SumNative.fold_source
#print axioms PV_B1_SumNative.limb_source
#print axioms PV_B1_SumNative.op230_source
#print axioms PV_B1_SumOriginal.exact_length
#print axioms PV_B1_SumOriginal.op230_source
#print axioms PV_B1_SumOriginal.wrong_length
#print axioms PV_B1_Transport.array_index
#print axioms PV_B1_Transport.array_repeat
#print axioms PV_B1_Transport.array_roundtrip
#print axioms PV_B1_Transport.array_set
#print axioms PV_B1_Transport.result_bind
#print axioms PV_B1_Transport.result_comp
#print axioms PV_B1_Transport.result_identity
#print axioms PV_B1_Transport.result_roundtrip
#print axioms PV_B1_Transport.slice_index
#print axioms PV_B1_Transport.slice_length
#print axioms PV_B1_Transport.slice_roundtrip
#print axioms PV_CBL_ArrayKernel.array_reference
#print axioms PV_CBL_ArrayKernel.array_reference_loop
#print axioms PV_CBL_ArrayKernel.array_reference_loop.body
#print axioms PV_Op223_Applied.aspis_core.field.CM31.ZERO
#print axioms PV_Op223_Applied.aspis_core.field.CM31.add
#print axioms PV_Op223_Applied.aspis_core.field.CM31.from_m31
#print axioms PV_Op223_Applied.aspis_core.field.CM31.mul
#print axioms PV_Op223_Applied.aspis_core.field.CM31.mul_m31
#print axioms PV_Op223_Applied.aspis_core.field.CM31.sub
#print axioms PV_Op223_Applied.aspis_core.field.M31.ZERO
#print axioms PV_Op223_Applied.aspis_core.field.M31.add
#print axioms PV_Op223_Applied.aspis_core.field.M31.double
#print axioms PV_Op223_Applied.aspis_core.field.M31.mul
#print axioms PV_Op223_Applied.aspis_core.field.M31.reduce_u64
#print axioms PV_Op223_Applied.aspis_core.field.M31.sub
#print axioms PV_Op223_Applied.aspis_core.field.P
#print axioms PV_Op223_Applied.aspis_core.field.QM31.add
#print axioms PV_Op223_Applied.aspis_core.field.QM31.from_cm31
#print axioms PV_Op223_Applied.aspis_core.field.QM31.mul
#print axioms PV_Op223_Applied.aspis_core.field.QM31.mul_m31
#print axioms PV_Op223_Applied.aspis_core.field.ct.add
#print axioms PV_Op223_Applied.aspis_core.field.ct.reduce64
#print axioms PV_Op223_Applied.aspis_core.field.ct.sub
#print axioms PV_Op223_Applied.aspis_core.field.ct.subtract_p
#print axioms PV_Op223_Applied.aspis_core.field.mul_by_r
#print axioms PV_Op223_Applied.aspis_core.field.reduce_u64
#print axioms PV_Op223_Applied.prover_shared.compress_tagged_tuple
#print axioms PV_Op223_Applied.prover_shared.compress_tagged_tuple_loop
#print axioms PV_Op223_Applied.prover_shared.compress_tagged_tuple_loop.body
#print axioms R1Z.PV_AL_BlockCodec.encode
#print axioms R1Z.PV_AL_BlockCodec.flatten_encode
#print axioms R1Z.PV_CBL_ArrayPrefix.advance
#print axioms R1Z.PV_CBL_ArrayPrefix.copied
#print axioms R1Z.PV_CBL_ArrayPrefix.initial
#print axioms R1Z.PV_CBL_ArrayPrefix.set_get
#print axioms R1Z.PV_CBL_GenericArrayFlatten.even
#print axioms R1Z.PV_CBL_GenericArrayFlatten.even_length
#print axioms R1Z.PV_CBL_GenericArrayFlatten.odd
#print axioms R1Z.PV_CBL_GenericArrayFlatten.odd_length
#print axioms R1Z.PV_CBL_GenericArrayPower.Storage
#print axioms R1Z.PV_CBL_GenericArrayPower.flatten
#print axioms R1Z.PV_CBL_GenericArrayPower.length
#print axioms R1Z.PV_CBL_LibraryShapeTypes.array_carrier
#print axioms R1Z.PV_CBL_LibraryShapeTypes.buffer_carrier
#print axioms R1Z.PV_CBL_LibraryShapes.Buffer
#print axioms R1Z.PV_CBL_LibraryShapes.CtWrapper
#print axioms R1Z.PV_CBL_LibraryShapes.Even
#print axioms R1Z.PV_CBL_LibraryShapes.GenericArray
#print axioms R1Z.PV_CBL_LibraryShapes.Odd
#print axioms R1Z.PV_CBL_LibraryShapes.Wrapper
#print axioms R1Z.PV_CBL_PadListFacts.ext
#print axioms R1Z.PV_CBL_PadListFacts.get_bang
#print axioms R1Z.PV_CBL_PaddingModel.blocks
#print axioms R1Z.PV_CBL_PaddingModel.delimited
#print axioms R1Z.PV_CBL_PaddingModel.first
#print axioms R1Z.PV_CBL_PaddingModel.retained
#print axioms R1Z.PV_CBL_PaddingModel.second
#print axioms R1Z.PV_CBL_WrapperReference.finalize
#print axioms R1Z.PV_CBL_WrapperReference.makeDefault
#print axioms R1Z.PV_DL_ArrayShape.Carrier
#print axioms R1Z.PV_DL_ArrayShape.Shape
#print axioms R1Z.PV_DL_ArrayShape.build
#print axioms R1Z.PV_DL_ArrayShape.flatten
#print axioms R1Z.PV_DL_ArrayShape.flatten_build
#print axioms R1Z.PV_DL_ArrayShape.length
#print axioms R1Z.PV_DL_ArrayShape.out28
#print axioms R1Z.PV_DL_ArrayShape.out32
#print axioms R1Z.PV_DL_ArrayShape.reconstruct
#print axioms R1Z.PV_DL_ArrayShape.size
#print axioms R1Z.PV_DL_ArrayShape.size28
#print axioms R1Z.PV_DL_ArrayShape.size32
#print axioms R1Z.PV_DL_CtCarrier.adapted
#print axioms R1Z.PV_DL_CtCarrier.callback
#print axioms R1Z.PV_DL_CtCarrier.complete
#print axioms R1Z.PV_DL_CtCarrier.decoded
#print axioms R1Z.PV_DL_CtCarrier.initial
#print axioms R1Z.PV_DL_CtCarrier.initial_byte
#print axioms R1Z.PV_DL_CtCarrier.value
#print axioms R1Z.PV_DL_CtFinal.complete
#print axioms R1Z.PV_DL_CtFinal.output_shape
#print axioms R1Z.PV_DL_CtFinal.reference
#print axioms R1Z.PV_DL_CtFinal.restoration
#print axioms R1Z.PV_DL_CtFinal.value
#print axioms R1Z.PV_DL_CtSelected.Types
#print axioms R1Z.PV_DL_CtSelected.direction
#print axioms R1Z.PV_DL_CtSelected.dispatch
#print axioms R1Z.PV_DL_CtSelected.dispatch_source
#print axioms R1Z.PV_DL_CtSelected.finisher
#print axioms R1Z.PV_DL_CtSelected.selected
#print axioms R1Z.PV_DL_CtSelected.selected_native
#print axioms R1Z.PV_DL_DefaultBuffer.bytes
#print axioms R1Z.PV_DL_DefaultBuffer.divergence
#print axioms R1Z.PV_DL_DefaultBuffer.failure
#print axioms R1Z.PV_DL_DefaultBuffer.initial
#print axioms R1Z.PV_DL_DefaultBuffer.model
#print axioms R1Z.PV_DL_DefaultBuffer.nonvacuous
#print axioms R1Z.PV_DL_DefaultBuffer.position
#print axioms R1Z.PV_DL_DefaultBuffer.success
#print axioms R1Z.PV_DL_DefaultBuffer.zeroStorage
#print axioms R1Z.PV_DL_DefaultCallback.Limit
#print axioms R1Z.PV_DL_DefaultCallback.callback
#print axioms R1Z.PV_DL_DefaultCallback.size
#print axioms R1Z.PV_DL_DefaultSelected.dispatch
#print axioms R1Z.PV_DL_DefaultSelected.dispatch_source
#print axioms R1Z.PV_DL_DefaultSelected.selected
#print axioms R1Z.PV_DL_Forwarding.ct
#print axioms R1Z.PV_DL_Forwarding.ct_length
#print axioms R1Z.PV_DL_Forwarding.ct_restoration
#print axioms R1Z.PV_DL_Forwarding.failure
#print axioms R1Z.PV_DL_Forwarding.output
#print axioms R1Z.PV_DL_StorageBuild.build
#print axioms R1Z.PV_DL_StorageBuild.flatten_build
#print axioms R1Z.PV_DL_StorageBuild.from32
#print axioms R1Z.PV_DL_StorageBuild.from32_value
#print axioms R1Z.PV_DL_StorageBuild.reconstruct
#print axioms R1Z.PV_DL_StorageBuild.to64
#print axioms R1Z.PV_DL_Truncation.full
#print axioms R1Z.PV_DL_Truncation.left_source
#print axioms R1Z.PV_DL_Truncation.length
#print axioms R1Z.PV_DL_Truncation.right_source
#print axioms R1Z.PV_DL_Truncation.value
#print axioms R1Z.PV_RDB2_Alignment.allocator_argument
#print axioms R1Z.PV_RDB2_Alignment.max_size_transport
#print axioms R1Z.PV_RDB2_Alignment.nonzero_accessor_complete
#print axioms R1Z.PV_RDB2_Alignment.positive
#print axioms R1Z.PV_RDB2_Alignment.within_half_word
#print axioms R1Z.PV_RDB2_Atomic.load_complete
#print axioms R1Z.PV_RDB2_Atomic.new_complete
#print axioms R1Z.PV_RDB2_Atomic.new_then_load
#print axioms R1Z.PV_RDB2_Compress.body
#print axioms R1Z.PV_RDB2_Compress.callback_removed
#print axioms R1Z.PV_RDB2_Compress.complete
#print axioms R1Z.PV_RDB2_Compress.installed
#print axioms R1Z.PV_RDB2_Compress.loop
#print axioms R1Z.PV_RDB2_ConstructorEffects.from_mut_complete
#print axioms R1Z.PV_RDB2_ConstructorEffects.new_unchecked_complete
#print axioms R1Z.PV_RDB2_ConstructorEffects.slice_complete
#print axioms R1Z.PV_RDB2_ConstructorEffects.slice_nonzero
#print axioms R1Z.PV_RDB2_ConstructorEffects.slice_provenance
#print axioms R1Z.PV_RDB2_ConstructorEffects.without_provenance_complete
#print axioms R1Z.PV_RDB2_CopyEffects.copied_destination
#print axioms R1Z.PV_RDB2_CopyEffects.copy_complete
#print axioms R1Z.PV_RDB2_CopyEffects.copy_frame
#print axioms R1Z.PV_RDB2_CopyEffects.copy_rejected
#print axioms R1Z.PV_RDB2_CopyEffects.destination_length
#print axioms R1Z.PV_RDB2_CopyEffects.fill_cell
#print axioms R1Z.PV_RDB2_CopyEffects.fill_complete
#print axioms R1Z.PV_RDB2_CopyEffects.initialized32
#print axioms R1Z.PV_RDB2_CopyEffects.range_complete
#print axioms R1Z.PV_RDB2_CopyEffects.range_rejected
#print axioms R1Z.PV_RDB2_CopyEffects.source_preserved
#print axioms R1Z.PV_RDB2_CtCopy.complete_frame
#print axioms R1Z.PV_RDB2_CtCopy.copy_complete
#print axioms R1Z.PV_RDB2_CtCopy.returned_bytes
#print axioms R1Z.PV_RDB2_CtCopy.returned_length
#print axioms R1Z.PV_RDB2_CtCopy.subtraction
#print axioms R1Z.PV_RDB2_CtCopy.view
#print axioms R1Z.PV_RDB2_Fold.complete
#print axioms R1Z.PV_RDB2_Fold.increment
#print axioms R1Z.PV_RDB2_Fold.initial
#print axioms R1Z.PV_RDB2_Fold.length_from_pointers
#print axioms R1Z.PV_RDB2_Fold.offset_alignment
#print axioms R1Z.PV_RDB2_Fold.offset_provenance
#print axioms R1Z.PV_RDB2_Fold.qm31_read_bounds
#print axioms R1Z.PV_RDB2_GlobalAlloc.allocate_complete
#print axioms R1Z.PV_RDB2_GlobalAlloc.null_is_allocation_error
#print axioms R1Z.PV_RDB2_GlobalAlloc.runtime_complete
#print axioms R1Z.PV_RDB2_GlobalAlloc.zero_no_allocator_call
#print axioms R1Z.PV_RDB2_Index.guarded
#print axioms R1Z.PV_RDB2_Index.increment_bound
#print axioms R1Z.PV_RDB2_Index.index_complete
#print axioms R1Z.PV_RDB2_Index.read_copy_complete
#print axioms R1Z.PV_RDB2_Index.rejected
#print axioms R1Z.PV_RDB2_Layout.same_failure
#print axioms R1Z.PV_RDB2_Layout.same_result
#print axioms R1Z.PV_RDB2_LayoutGeneral.after_success
#print axioms R1Z.PV_RDB2_LayoutGeneral.before_after_size
#print axioms R1Z.PV_RDB2_LayoutGeneral.before_success
#print axioms R1Z.PV_RDB2_LayoutGeneral.historical_closed
#print axioms R1Z.PV_RDB2_LayoutGeneral.padded_complete
#print axioms R1Z.PV_RDB2_LayoutGeneral.unpadded_results
#print axioms R1Z.PV_RDB2_LayoutGuards.complete_effect
#print axioms R1Z.PV_RDB2_LayoutGuards.from_size_alignment
#print axioms R1Z.PV_RDB2_LayoutGuards.is_size_align_valid
#print axioms R1Z.PV_RDB2_LayoutGuards.summation_guard
#print axioms R1Z.PV_RDB2_LayoutGuards.unchecked_sub_bound
#print axioms R1Z.PV_RDB2_LayoutPad.complete
#print axioms R1Z.PV_RDB2_LayoutPad.complete_effect
#print axioms R1Z.PV_RDB2_LayoutPad.unchanged_alignment
#print axioms R1Z.PV_RDB2_LayoutRepeat.checked_mul_layout
#print axioms R1Z.PV_RDB2_LayoutRepeat.layout_array
#print axioms R1Z.PV_RDB2_LayoutRepeat.padded_complete
#print axioms R1Z.PV_RDB2_LayoutRepeat.padded_effect
#print axioms R1Z.PV_RDB2_MutBorrow.backward_bounds
#print axioms R1Z.PV_RDB2_MutBorrow.cursor_retained
#print axioms R1Z.PV_RDB2_MutBorrow.forward_bounds
#print axioms R1Z.PV_RDB2_MutBorrow.frame
#print axioms R1Z.PV_RDB2_MutBorrow.written
#print axioms R1Z.PV_RDB2_MutMixed.back_after_front_write
#print axioms R1Z.PV_RDB2_MutMixed.disjoint_writes
#print axioms R1Z.PV_RDB2_MutMixed.mixed_indices_distinct
#print axioms R1Z.PV_RDB2_MutMixed.restore_commutes
#print axioms R1Z.PV_RDB2_NonNull.cast_complete
#print axioms R1Z.PV_RDB2_NonNull.cast_metadata
#print axioms R1Z.PV_RDB2_NonNull.cast_provenance
#print axioms R1Z.PV_RDB2_NonNull.from_ref_complete
#print axioms R1Z.PV_RDB2_NonNull.iterator_constructor
#print axioms R1Z.PV_RDB2_NonNull.nonnull_preserved
#print axioms R1Z.PV_RDB2_Pointer.advance_address
#print axioms R1Z.PV_RDB2_Pointer.advance_valid
#print axioms R1Z.PV_RDB2_Pointer.cast_complete
#print axioms R1Z.PV_RDB2_Pointer.next_complete
#print axioms R1Z.PV_RDB2_Pointer.next_storage
#print axioms R1Z.PV_RDB2_Pointer.pack_projection
#print axioms R1Z.PV_RDB2_Pointer.pointer_eq_end
#print axioms R1Z.PV_RDB2_Pointer.read_bounds
#print axioms R1Z.PV_RDB2_PointerBridge.cast_complete
#print axioms R1Z.PV_RDB2_PointerBridge.constructor_complete
#print axioms R1Z.PV_RDB2_PointerBridge.live_provenance
#print axioms R1Z.PV_RDB2_PointerBridge.slice_complete
#print axioms R1Z.PV_RDB2_RawVec.allocator_projection
#print axioms R1Z.PV_RDB2_RawVec.empty_capacity
#print axioms R1Z.PV_RDB2_RawVec.new_in_complete
#print axioms R1Z.PV_RDB2_RawVec.new_in_no_allocation
#print axioms R1Z.PV_RDB2_Realloc.complete
#print axioms R1Z.PV_RDB2_Realloc.new_suffix_uninitialized
#print axioms R1Z.PV_RDB2_Realloc.prefix_preserved
#print axioms R1Z.PV_RDB2_Realloc.shrink_discards_only_suffix
#print axioms R1Z.PV_RDB2_ResultEffects.congruence
#print axioms R1Z.PV_RDB2_ResultEffects.divergence_prefix
#print axioms R1Z.PV_RDB2_ResultEffects.failure_frame
#print axioms R1Z.PV_RDB2_ResultEffects.left_identity
#print axioms R1Z.PV_RDB2_SumDeployed.complete
#print axioms R1Z.PV_RDB2_SumDeployed.compressor_retained
#print axioms R1Z.PV_RDB2_SumDeployed.fold_value
#print axioms R1Z.PV_RDB2_SumDeployed.installed
#print axioms R1Z.PV_RDB2_SumDeployed.storage_and_value
#print axioms R1Z.PV_RDB2_SumDeployed.wrong_length_no_read
#print axioms R1Z.PV_RDB2_Truncate.complete
#print axioms R1Z.PV_RDB2_Truncate.no_drop_when_extending
#print axioms R1Z.PV_RDB2_Truncate.reduced_before_drop
#print axioms R1Z.PV_RDB2_VecBorrow.complete_return
#print axioms R1Z.PV_RDB2_VecBorrow.every_write
#print axioms R1Z.PV_RDB2_VecBorrow.initialized_read
#print axioms R1Z.PV_RDB2_VecBorrow.no_spare_exposure
#print axioms R1Z.PV_RDB2_VecBorrow.roundtrip
