import R1Z.PV_DL_ArrayNative
import R1Z.PV_DL_ArrayOwnership
import R1Z.PV_DL_ArrayShape
import R1Z.PV_DL_ArrayTransfer
import R1Z.PV_DL_BatchPlan
import R1Z.PV_DL_CompressionTrace
import R1Z.PV_DL_CtCarrier
import R1Z.PV_DL_CtFinal
import R1Z.PV_DL_CtSelected
import R1Z.PV_DL_Default
import R1Z.PV_DL_DefaultBuffer
import R1Z.PV_DL_DefaultCallback
import R1Z.PV_DL_DefaultLaw
import R1Z.PV_DL_DefaultNative
import R1Z.PV_DL_DefaultSelected
import R1Z.PV_DL_DefaultTypes
import R1Z.PV_DL_DigestFinal
import R1Z.PV_DL_EncoderBasis
import R1Z.PV_DL_EncoderBounds
import R1Z.PV_DL_EncoderControl
import R1Z.PV_DL_EncoderFill
import R1Z.PV_DL_EncoderFold
import R1Z.PV_DL_EncoderMutation
import R1Z.PV_DL_EncoderNative
import R1Z.PV_DL_EncoderPairs
import R1Z.PV_DL_EncoderRange
import R1Z.PV_DL_EncoderSelected
import R1Z.PV_DL_EncoderZip
import R1Z.PV_DL_FinalizeParam
import R1Z.PV_DL_FixedFinal
import R1Z.PV_DL_Forwarding
import R1Z.PV_DL_LengthEncoding
import R1Z.PV_DL_NativeCohort
import R1Z.PV_DL_OwnershipEffects
import R1Z.PV_DL_ShaBranches
import R1Z.PV_DL_ShaFinal
import R1Z.PV_DL_ShaRestoration
import R1Z.PV_DL_ShaSelected
import R1Z.PV_DL_ShaSerialize
import R1Z.PV_DL_StorageBuild
import R1Z.PV_DL_StorageIdentity
import R1Z.PV_DL_Truncation
import R1Z.PV_DL_UpdateCarrier
import R1Z.PV_DL_UpdateCopy
import R1Z.PV_DL_UpdateEvents
import R1Z.PV_DL_UpdatePlan
import R1Z.PV_DL_UpdateSelected
import R1Z.PV_DL_UpdateViews
import R1Z.PV_DL_Wrap
import R1Z.PV_DL_WrapLaw
import R1Z.PV_DL_WrapTypes
namespace R1Z.PV_DL_ResumeAudit
set_option autoImplicit false
#print axioms R1Z.PV_DL_ArrayNative.pack
#print axioms R1Z.PV_DL_ArrayNative.reference
#print axioms R1Z.PV_DL_ArrayNative.source_reference
#print axioms R1Z.PV_DL_ArrayNative.selected
#print axioms R1Z.PV_DL_ArrayNative.selected_native
#print axioms R1Z.PV_DL_ArrayNative.nonvacuous
#print axioms R1Z.PV_DL_ArrayOwnership.value
#print axioms R1Z.PV_DL_ArrayOwnership.rejection
#print axioms R1Z.PV_DL_ArrayOwnership.success
#print axioms R1Z.PV_DL_ArrayOwnership.complete
#print axioms R1Z.PV_DL_ArrayShape.Shape
#print axioms R1Z.PV_DL_ArrayShape.size
#print axioms R1Z.PV_DL_ArrayShape.Carrier
#print axioms R1Z.PV_DL_ArrayShape.flatten
#print axioms R1Z.PV_DL_ArrayShape.build
#print axioms R1Z.PV_DL_ArrayShape.length
#print axioms R1Z.PV_DL_ArrayShape.flatten_build
#print axioms R1Z.PV_DL_ArrayShape.reconstruct
#print axioms R1Z.PV_DL_ArrayShape.out28
#print axioms R1Z.PV_DL_ArrayShape.out32
#print axioms R1Z.PV_DL_ArrayShape.size28
#print axioms R1Z.PV_DL_ArrayShape.size32
#print axioms R1Z.PV_DL_ArrayTransfer.drain
#print axioms R1Z.PV_DL_ArrayTransfer.exact_transfer
#print axioms R1Z.PV_DL_ArrayTransfer.zero_live_drops
#print axioms R1Z.PV_DL_ArrayTransfer.sequential
#print axioms R1Z.PV_DL_ArrayTransfer.bulk
#print axioms R1Z.PV_DL_ArrayTransfer.complete
#print axioms R1Z.PV_DL_BatchPlan.bulk
#print axioms R1Z.PV_DL_BatchPlan.reassemble
#print axioms R1Z.PV_DL_BatchPlan.remainder
#print axioms R1Z.PV_DL_BatchPlan.events
#print axioms R1Z.PV_DL_BatchPlan.run
#print axioms R1Z.PV_DL_BatchPlan.no_bulk
#print axioms R1Z.PV_DL_BatchPlan.single_bulk
#print axioms R1Z.PV_DL_CompressionTrace.run
#print axioms R1Z.PV_DL_CompressionTrace.empty
#print axioms R1Z.PV_DL_CompressionTrace.append
#print axioms R1Z.PV_DL_CompressionTrace.event_transport
#print axioms R1Z.PV_DL_CompressionTrace.backend_instances
#print axioms R1Z.PV_DL_CtCarrier.initial
#print axioms R1Z.PV_DL_CtCarrier.initial_byte
#print axioms R1Z.PV_DL_CtCarrier.adapted
#print axioms R1Z.PV_DL_CtCarrier.callback
#print axioms R1Z.PV_DL_CtCarrier.value
#print axioms R1Z.PV_DL_CtCarrier.complete
#print axioms R1Z.PV_DL_CtCarrier.decoded
#print axioms R1Z.PV_DL_CtFinal.reference
#print axioms R1Z.PV_DL_CtFinal.value
#print axioms R1Z.PV_DL_CtFinal.complete
#print axioms R1Z.PV_DL_CtFinal.restoration
#print axioms R1Z.PV_DL_CtFinal.output_shape
#print axioms R1Z.PV_DL_CtSelected.Types
#print axioms R1Z.PV_DL_CtSelected.dispatch
#print axioms R1Z.PV_DL_CtSelected.dispatch_source
#print axioms R1Z.PV_DL_CtSelected.finisher
#print axioms R1Z.PV_DL_CtSelected.direction
#print axioms R1Z.PV_DL_CtSelected.selected
#print axioms R1Z.PV_DL_CtSelected.selected_native
#print axioms PV_DL_Default.default_reference
#print axioms R1Z.PV_DL_DefaultBuffer.zeroStorage
#print axioms R1Z.PV_DL_DefaultBuffer.initial
#print axioms R1Z.PV_DL_DefaultBuffer.model
#print axioms R1Z.PV_DL_DefaultBuffer.bytes
#print axioms R1Z.PV_DL_DefaultBuffer.success
#print axioms R1Z.PV_DL_DefaultBuffer.failure
#print axioms R1Z.PV_DL_DefaultBuffer.divergence
#print axioms R1Z.PV_DL_DefaultBuffer.nonvacuous
#print axioms R1Z.PV_DL_DefaultBuffer.position
#print axioms R1Z.PV_DL_DefaultCallback.Limit
#print axioms R1Z.PV_DL_DefaultCallback.size
#print axioms R1Z.PV_DL_DefaultCallback.callback
#print axioms R1Z.PV_DL_DefaultLaw.initialState
#print axioms R1Z.PV_DL_DefaultLaw.snapshot
#print axioms R1Z.PV_DL_DefaultLaw.source
#print axioms R1Z.PV_DL_DefaultLaw.nonvacuous
#print axioms R1Z.PV_DL_DefaultLaw.empty_position
#print axioms R1Z.PV_DL_DefaultLaw.zero_blocks
#print axioms R1Z.PV_DL_DefaultLaw.backend_independent
#print axioms R1Z.PV_DL_DefaultNative.bufferKind
#print axioms R1Z.PV_DL_DefaultNative.native_callback
#print axioms R1Z.PV_DL_DefaultNative.consumed
#print axioms R1Z.PV_DL_DefaultSelected.dispatch
#print axioms R1Z.PV_DL_DefaultSelected.dispatch_source
#print axioms R1Z.PV_DL_DefaultSelected.selected
#print axioms R1Z.PV_DL_DigestFinal.reference
#print axioms R1Z.PV_DL_DigestFinal.forwarding
#print axioms R1Z.PV_DL_DigestFinal.complete
#print axioms R1Z.PV_DL_DigestFinal.dispatch
#print axioms R1Z.PV_DL_DigestFinal.dispatch_source
#print axioms R1Z.PV_DL_DigestFinal.finisher
#print axioms R1Z.PV_DL_DigestFinal.selected
#print axioms R1Z.PV_DL_DigestFinal.selected_native
#print axioms R1Z.PV_DL_DigestFinal.nonvacuous
#print axioms R1Z.PV_DL_EncoderBasis.advance
#print axioms R1Z.PV_DL_EncoderBasis.half_rank
#print axioms R1Z.PV_DL_EncoderBasis.advance_val
#print axioms R1Z.PV_DL_EncoderBasis.factor
#print axioms R1Z.PV_DL_EncoderBasis.finite
#print axioms R1Z.PV_DL_EncoderBasis.source
#print axioms R1Z.PV_DL_EncoderBasis.value
#print axioms R1Z.PV_DL_EncoderBasis.basis_source
#print axioms R1Z.PV_DL_EncoderBasis.native_min
#print axioms R1Z.PV_DL_EncoderBounds.cells
#print axioms R1Z.PV_DL_EncoderBounds.target_val
#print axioms R1Z.PV_DL_EncoderBounds.writes
#print axioms R1Z.PV_DL_EncoderControl.duplicate
#print axioms R1Z.PV_DL_EncoderControl.value
#print axioms R1Z.PV_DL_EncoderControl.source_reference
#print axioms R1Z.PV_DL_EncoderControl.inputs_nonempty
#print axioms R1Z.PV_DL_EncoderFill.finite
#print axioms R1Z.PV_DL_EncoderFill.source
#print axioms R1Z.PV_DL_EncoderFold.step
#print axioms R1Z.PV_DL_EncoderFold.finite
#print axioms R1Z.PV_DL_EncoderFold.source
#print axioms R1Z.PV_DL_EncoderMutation.read
#print axioms R1Z.PV_DL_EncoderMutation.restoration
#print axioms R1Z.PV_DL_EncoderMutation.changed_cell
#print axioms R1Z.PV_DL_EncoderNative.selected_native
#print axioms R1Z.PV_DL_EncoderNative.run
#print axioms R1Z.PV_DL_EncoderNative.suffix
#print axioms R1Z.PV_DL_EncoderNative.fold
#print axioms R1Z.PV_DL_EncoderNative.value
#print axioms R1Z.PV_DL_EncoderNative.source_reference
#print axioms R1Z.PV_DL_EncoderPairs.chunks
#print axioms R1Z.PV_DL_EncoderPairs.length
#print axioms R1Z.PV_DL_EncoderPairs.coordinate
#print axioms R1Z.PV_DL_EncoderPairs.message_count
#print axioms R1Z.PV_DL_EncoderRange.advance
#print axioms R1Z.PV_DL_EncoderRange.advance_val
#print axioms R1Z.PV_DL_EncoderRange.even
#print axioms R1Z.PV_DL_EncoderRange.odd
#print axioms R1Z.PV_DL_EncoderSelected.selected
#print axioms R1Z.PV_DL_EncoderSelected.selected_callback
#print axioms R1Z.PV_DL_EncoderSelected.consumed
#print axioms R1Z.PV_DL_EncoderSelected.pairs_complete
#print axioms R1Z.PV_DL_EncoderZip.entries
#print axioms R1Z.PV_DL_EncoderZip.count
#print axioms R1Z.PV_DL_EncoderZip.coordinate
#print axioms R1Z.PV_DL_EncoderZip.applyEntry
#print axioms R1Z.PV_DL_EncoderZip.step
#print axioms R1Z.PV_DL_FinalizeParam.reference
#print axioms R1Z.PV_DL_FinalizeParam.model
#print axioms R1Z.PV_DL_FinalizeParam.source
#print axioms R1Z.PV_DL_FinalizeParam.callback_count
#print axioms R1Z.PV_DL_FixedFinal.value
#print axioms R1Z.PV_DL_FixedFinal.complete
#print axioms R1Z.PV_DL_FixedFinal.dispatch
#print axioms R1Z.PV_DL_FixedFinal.dispatch_source
#print axioms R1Z.PV_DL_FixedFinal.finisher
#print axioms R1Z.PV_DL_FixedFinal.selected
#print axioms R1Z.PV_DL_FixedFinal.selected_native
#print axioms R1Z.PV_DL_Forwarding.output
#print axioms R1Z.PV_DL_Forwarding.failure
#print axioms R1Z.PV_DL_Forwarding.ct
#print axioms R1Z.PV_DL_Forwarding.ct_restoration
#print axioms R1Z.PV_DL_Forwarding.ct_length
#print axioms R1Z.PV_DL_LengthEncoding.suffix
#print axioms R1Z.PV_DL_LengthEncoding.suffix_length
#print axioms R1Z.PV_DL_LengthEncoding.length_value
#print axioms R1Z.PV_DL_LengthEncoding.finalize
#print axioms R1Z.PV_DL_LengthEncoding.source
#print axioms R1Z.PV_DL_NativeCohort.Types
#print axioms R1Z.PV_DL_NativeCohort.CoreBase
#print axioms R1Z.PV_DL_NativeCohort.selected
#print axioms R1Z.PV_DL_NativeCohort.slots
#print axioms R1Z.PV_DL_OwnershipEffects.Outcome
#print axioms R1Z.PV_DL_OwnershipEffects.erase
#print axioms R1Z.PV_DL_OwnershipEffects.unitEffect
#print axioms R1Z.PV_DL_OwnershipEffects.sequence
#print axioms R1Z.PV_DL_OwnershipEffects.left_identity
#print axioms R1Z.PV_DL_OwnershipEffects.right_identity
#print axioms R1Z.PV_DL_OwnershipEffects.byte_buffer_drop_order
#print axioms R1Z.PV_DL_OwnershipEffects.controller
#print axioms R1Z.PV_DL_OwnershipEffects.native
#print axioms R1Z.PV_DL_OwnershipEffects.reference
#print axioms R1Z.PV_DL_OwnershipEffects.complete
#print axioms R1Z.PV_DL_OwnershipEffects.complete_result
#print axioms R1Z.PV_DL_OwnershipEffects.no_drop
#print axioms R1Z.PV_DL_ShaBranches.padding
#print axioms R1Z.PV_DL_ShaBranches.suffix_fits
#print axioms R1Z.PV_DL_ShaBranches.word_chunks
#print axioms R1Z.PV_DL_ShaBranches.word_indices
#print axioms R1Z.PV_DL_ShaFinal.identity_run
#print axioms R1Z.PV_DL_ShaFinal.nonvacuous
#print axioms R1Z.PV_DL_ShaFinal.reference
#print axioms R1Z.PV_DL_ShaFinal.value
#print axioms R1Z.PV_DL_ShaFinal.source_reference
#print axioms R1Z.PV_DL_ShaRestoration.position
#print axioms R1Z.PV_DL_ShaRestoration.suffix
#print axioms R1Z.PV_DL_ShaRestoration.retained
#print axioms R1Z.PV_DL_ShaRestoration.retained_length
#print axioms R1Z.PV_DL_ShaRestoration.buffer_restored
#print axioms R1Z.PV_DL_ShaRestoration.output_restored
#print axioms R1Z.PV_DL_ShaRestoration.selected_native
#print axioms R1Z.PV_DL_ShaSelected.Types
#print axioms R1Z.PV_DL_ShaSelected.Output32
#print axioms R1Z.PV_DL_ShaSelected.callback
#print axioms R1Z.PV_DL_ShaSelected.value
#print axioms R1Z.PV_DL_ShaSelected.source_reference
#print axioms R1Z.PV_DL_ShaSelected.selected
#print axioms R1Z.PV_DL_ShaSelected.selected_native
#print axioms R1Z.PV_DL_ShaSelected.overwrites
#print axioms R1Z.PV_DL_ShaSerialize.bytes
#print axioms R1Z.PV_DL_ShaSerialize.reference
#print axioms R1Z.PV_DL_ShaSerialize.source
#print axioms R1Z.PV_DL_ShaSerialize.length
#print axioms R1Z.PV_DL_ShaSerialize.array
#print axioms R1Z.PV_DL_ShaSerialize.total
#print axioms R1Z.PV_DL_StorageBuild.build
#print axioms R1Z.PV_DL_StorageBuild.flatten_build
#print axioms R1Z.PV_DL_StorageBuild.reconstruct
#print axioms R1Z.PV_DL_StorageBuild.from32
#print axioms R1Z.PV_DL_StorageBuild.to64
#print axioms R1Z.PV_DL_StorageBuild.from32_value
#print axioms R1Z.PV_DL_StorageIdentity.zero_array
#print axioms R1Z.PV_DL_StorageIdentity.left_half
#print axioms R1Z.PV_DL_StorageIdentity.right_half
#print axioms R1Z.PV_DL_StorageIdentity.injective
#print axioms R1Z.PV_DL_StorageIdentity.rebuild
#print axioms R1Z.PV_DL_Truncation.value
#print axioms R1Z.PV_DL_Truncation.length
#print axioms R1Z.PV_DL_Truncation.full
#print axioms R1Z.PV_DL_Truncation.left_source
#print axioms R1Z.PV_DL_Truncation.right_source
#print axioms R1Z.PV_DL_UpdateCarrier.blockList
#print axioms R1Z.PV_DL_UpdateCarrier.block_decoding
#print axioms R1Z.PV_DL_UpdateCarrier.decoded_blocks
#print axioms R1Z.PV_DL_UpdateCarrier.compress
#print axioms R1Z.PV_DL_UpdateCarrier.block_count
#print axioms R1Z.PV_DL_UpdateCarrier.compression_call
#print axioms R1Z.PV_DL_UpdateCarrier.native_batch_bound
#print axioms R1Z.PV_DL_UpdateCarrier.encode
#print axioms R1Z.PV_DL_UpdateCarrier.callback
#print axioms R1Z.PV_DL_UpdateCarrier.value
#print axioms R1Z.PV_DL_UpdateCarrier.complete
#print axioms R1Z.PV_DL_UpdateCarrier.encoding_valid
#print axioms R1Z.PV_DL_UpdateCarrier.decoded
#print axioms R1Z.PV_DL_UpdateCopy.cells
#print axioms R1Z.PV_DL_UpdateCopy.cells_value
#print axioms R1Z.PV_DL_UpdateCopy.loop
#print axioms R1Z.PV_DL_UpdateCopy.copy
#print axioms R1Z.PV_DL_UpdateCopy.bounds
#print axioms R1Z.PV_DL_UpdateEvents.Plumbing
#print axioms R1Z.PV_DL_UpdateEvents.step
#print axioms R1Z.PV_DL_UpdateEvents.fold
#print axioms R1Z.PV_DL_UpdateEvents.append
#print axioms R1Z.PV_DL_UpdateEvents.complete
#print axioms R1Z.PV_DL_UpdateEvents.pending
#print axioms R1Z.PV_DL_UpdatePlan.v233Specification
#print axioms R1Z.PV_DL_UpdatePlan.v233_native64
#print axioms R1Z.PV_DL_UpdatePlan.Plan
#print axioms R1Z.PV_DL_UpdatePlan.write
#print axioms R1Z.PV_DL_UpdatePlan.first
#print axioms R1Z.PV_DL_UpdatePlan.start
#print axioms R1Z.PV_DL_UpdatePlan.value
#print axioms R1Z.PV_DL_UpdatePlan.reference
#print axioms R1Z.PV_DL_UpdatePlan.source_reference
#print axioms R1Z.PV_DL_UpdatePlan.write_length
#print axioms R1Z.PV_DL_UpdatePlan.first_length
#print axioms R1Z.PV_DL_UpdatePlan.shape
#print axioms R1Z.PV_DL_UpdatePlan.run
#print axioms R1Z.PV_DL_UpdatePlan.model
#print axioms R1Z.PV_DL_UpdatePlan.complete
#print axioms R1Z.PV_DL_UpdateSelected.Types
#print axioms R1Z.PV_DL_UpdateSelected.dispatch
#print axioms R1Z.PV_DL_UpdateSelected.dispatch_source
#print axioms R1Z.PV_DL_UpdateSelected.updater
#print axioms R1Z.PV_DL_UpdateSelected.kindDispatch
#print axioms R1Z.PV_DL_UpdateSelected.native_kind
#print axioms R1Z.PV_DL_UpdateSelected.bufferKind
#print axioms R1Z.PV_DL_UpdateSelected.selected
#print axioms R1Z.PV_DL_UpdateSelected.retained_kind
#print axioms R1Z.PV_DL_UpdateSelected.selected_native
#print axioms R1Z.PV_DL_UpdateViews.views
#print axioms R1Z.PV_DL_UpdateViews.count
#print axioms R1Z.PV_DL_UpdateViews.joined
#print axioms R1Z.PV_DL_UpdateViews.coordinate
#print axioms R1Z.PV_DL_UpdateViews.byte
#print axioms R1Z.PV_DL_UpdateViews.lengths
#print axioms R1Z.PV_DL_UpdateViews.native_bulk
#print axioms R1Z.PV_DL_UpdateViews.native_block_lengths
#print axioms PV_DL_Wrap.wrap_reference
#print axioms R1Z.PV_DL_WrapLaw.observe
#print axioms R1Z.PV_DL_WrapLaw.observeReference
#print axioms R1Z.PV_DL_WrapLaw.source_reference
end R1Z.PV_DL_ResumeAudit

open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_ResumeReplay
set_option autoImplicit false
theorem encoder {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    PV_DL_EncoderNative.value inst q p=PV_CB_OwnedEncoder.owned.encoder inst q p :=
  PV_DL_EncoderNative.source_reference inst q p

theorem vector {T : Type} (N : Usize) (v : alloc.vec.Vec T) :
    PV_DL_ArrayNative.reference N v=ok (PV_DL_ArrayOwnership.value N v) :=
  PV_DL_ArrayNative.source_reference N v

theorem sha (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (core : PV_DL_ShaFinal.Core) (buffer : Array U8 64#usize) (pos : Usize) (h : pos.val<64) :
    PV_DL_ShaFinal.reference compress core buffer pos=PV_DL_ShaFinal.value compress core buffer pos :=
  PV_DL_ShaFinal.source_reference compress core buffer pos h

#print axioms R1Z.PV_DL_EncoderNative.selected_native
#print axioms R1Z.PV_DL_ArrayNative.selected_native
#print axioms R1Z.PV_DL_ShaRestoration.selected_native
#print axioms R1Z.PV_DL_DigestFinal.selected_native
#print axioms R1Z.PV_DL_FixedFinal.selected_native
#print axioms R1Z.PV_DL_UpdateSelected.selected_native
#print axioms R1Z.PV_DL_DefaultNative.consumed
#print axioms R1Z.PV_DL_CtSelected.selected_native
#print axioms R1Z.PV_DL_NativeCohort.slots
#print axioms encoder
#print axioms vector
#print axioms sha
end R1Z.PV_DL_ResumeReplay
