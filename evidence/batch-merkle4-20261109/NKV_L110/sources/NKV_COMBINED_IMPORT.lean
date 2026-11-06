import NKN_COMBINED_IMPORT
import NKL_COMBINED_IMPORT
import NKV_AbortPrefix
import NKV_ActiveStep
import NKV_BatchGeometry
import NKV_BoundedLoop
import NKV_ClassifiedBody
import NKV_ConcreteChildren
import NKV_ConcreteDomains
import NKV_CountCut
import NKV_CountInvocation
import NKV_ErrorKinds
import NKV_ExitTrace
import NKV_FRef
import NKV_KeyInvocation
import NKV_LeafBuild
import NKV_LeafHistory
import NKV_LeafInvocation
import NKV_LeafOrder
import NKV_LeafSlot
import NKV_LeafStep
import NKV_LeafTotal
import NKV_LeafTraversal
import NKV_LoopTransport
import NKV_OkTransport
import NKV_OuterSource
import NKV_OuterTotal
import NKV_PaddingChunks
import NKV_PaddingInstall
import NKV_PaddingValue
import NKV_ParentSource
import NKV_ParentTotal
import NKV_ParentTrace
import NKV_ProducerDomain
import NKV_Progress
import NKV_QueryPlan
import NKV_ReturnBoundary
import NKV_SlotInvocation
import NKV_StepErasure
import NKV_TailArithmetic
import NKV_TailContinue
import NKV_TailLoop
import NKV_TailModel
import NKV_TailProgram
import NKV_TailReject
import NKV_TailTotal
import NKV_TraceCases
import NKV_TreeBuild
import NKV_TreeEntry
import NKV_TreeErrors
import NKV_TreeModel
import NKV_TreeSource
import NKV_TreeTotal
import NKV_VerifyInvocation
set_option pp.proofs false
#print AspisR1.NCE_PaddingCuts.first_stop
#print axioms AspisR1.NCE_PaddingCuts.first_stop
#print AspisR1.NCE_PaddingCuts.run_eq
#print axioms AspisR1.NCE_PaddingCuts.run_eq
#print AspisR1.NCE_PaddingPhysical.chunk_sizes
#print axioms AspisR1.NCE_PaddingPhysical.chunk_sizes
#print AspisR1.NCE_PaddingPhysical.counted_suffix
#print axioms AspisR1.NCE_PaddingPhysical.counted_suffix
#print AspisR1.NCE_PaddingPhysical.exact_chunk_lengths
#print axioms AspisR1.NCE_PaddingPhysical.exact_chunk_lengths
#print AspisR1.NCE_PaddingPhysical.physical_run
#print axioms AspisR1.NCE_PaddingPhysical.physical_run
#print AspisR1.NCM_PaddingBytes.all_zero
#print axioms AspisR1.NCM_PaddingBytes.all_zero
#print AspisR1.NCM_PaddingBytes.scan
#print axioms AspisR1.NCM_PaddingBytes.scan
#print AspisR1.NCM_PaddingCover.member
#print axioms AspisR1.NCM_PaddingCover.member
#print AspisR1.NCM_PaddingCover.raw_zero
#print axioms AspisR1.NCM_PaddingCover.raw_zero
#print AspisR1.NCM_PaddingCover.zero
#print axioms AspisR1.NCM_PaddingCover.zero
#print AspisR1.NCM_PaddingPredicate.observation
#print axioms AspisR1.NCM_PaddingPredicate.observation
#print AspisR1.NCM_PaddingScan.native_value
#print axioms AspisR1.NCM_PaddingScan.native_value
#print AspisR1.NCM_PaddingScan.value
#print axioms AspisR1.NCM_PaddingScan.value
#print AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.RPx_Deployed.deployed
#print NKV_AbortPrefix.pending
#print axioms NKV_AbortPrefix.pending
#print NKV_AbortPrefix.take_prefix
#print axioms NKV_AbortPrefix.take_prefix
#print NKV_AbortPrefix.tx2
#print axioms NKV_AbortPrefix.tx2
#print NKV_ActiveStep.source
#print axioms NKV_ActiveStep.source
#print NKV_BatchGeometry.slot
#print axioms NKV_BatchGeometry.slot
#print NKV_BatchGeometry.span0
#print axioms NKV_BatchGeometry.span0
#print NKV_BatchGeometry.span1
#print axioms NKV_BatchGeometry.span1
#print NKV_BoundedLoop.classified
#print axioms NKV_BoundedLoop.classified
#print NKV_BoundedLoop.finite
#print axioms NKV_BoundedLoop.finite
#print NKV_BoundedLoop.source
#print axioms NKV_BoundedLoop.source
#print NKV_ClassifiedBody.no_lost_ok
#print axioms NKV_ClassifiedBody.no_lost_ok
#print NKV_ConcreteChildren.installed
#print axioms NKV_ConcreteChildren.installed
#print NKV_ConcreteChildren.source
#print axioms NKV_ConcreteChildren.source
#print NKV_ConcreteDomains.count
#print axioms NKV_ConcreteDomains.count
#print NKV_ConcreteDomains.leaf
#print axioms NKV_ConcreteDomains.leaf
#print NKV_ConcreteDomains.leaf_domains
#print axioms NKV_ConcreteDomains.leaf_domains
#print NKV_ConcreteDomains.opening
#print axioms NKV_ConcreteDomains.opening
#print NKV_ConcreteDomains.verifier_bytes
#print axioms NKV_ConcreteDomains.verifier_bytes
#print NKV_CountCut.missing
#print axioms NKV_CountCut.missing
#print NKV_CountCut.present
#print axioms NKV_CountCut.present
#print NKV_CountCut.source
#print axioms NKV_CountCut.source
#print NKV_CountInvocation.keys
#print axioms NKV_CountInvocation.keys
#print NKV_CountInvocation.missing
#print axioms NKV_CountInvocation.missing
#print NKV_CountInvocation.present
#print axioms NKV_CountInvocation.present
#print NKV_CountInvocation.read
#print axioms NKV_CountInvocation.read
#print NKV_CountInvocation.source
#print axioms NKV_CountInvocation.source
#print NKV_ErrorKinds.loop
#print axioms NKV_ErrorKinds.loop
#print NKV_ErrorKinds.step_error
#print axioms NKV_ErrorKinds.step_error
#print NKV_ErrorKinds.walk
#print axioms NKV_ErrorKinds.walk
#print NKV_ExitTrace.terminal
#print axioms NKV_ExitTrace.terminal
#print NKV_ExitTrace.transport
#print axioms NKV_ExitTrace.transport
#print NKV_ExitTrace.value
#print axioms NKV_ExitTrace.value
#print NKV_KeyInvocation.source
#print axioms NKV_KeyInvocation.source
#print NKV_LeafBuild.adopted
#print axioms NKV_LeafBuild.adopted
#print NKV_LeafBuild.chain
#print axioms NKV_LeafBuild.chain
#print NKV_LeafBuild.fold
#print axioms NKV_LeafBuild.fold
#print NKV_LeafHistory.complete
#print axioms NKV_LeafHistory.complete
#print NKV_LeafHistory.ordered_prefix
#print axioms NKV_LeafHistory.ordered_prefix
#print NKV_LeafInvocation.source
#print axioms NKV_LeafInvocation.source
#print NKV_LeafOrder.canonical
#print axioms NKV_LeafOrder.canonical
#print NKV_LeafOrder.key_bound
#print axioms NKV_LeafOrder.key_bound
#print NKV_LeafOrder.key_value
#print axioms NKV_LeafOrder.key_value
#print NKV_LeafOrder.nonempty
#print axioms NKV_LeafOrder.nonempty
#print NKV_LeafOrder.ordered
#print axioms NKV_LeafOrder.ordered
#print NKV_LeafOrder.positions_ordered
#print axioms NKV_LeafOrder.positions_ordered
#print NKV_LeafOrder.size
#print axioms NKV_LeafOrder.size
#print NKV_LeafSlot.rejected
#print axioms NKV_LeafSlot.rejected
#print NKV_LeafSlot.source
#print axioms NKV_LeafSlot.source
#print NKV_LeafStep.project_source
#print axioms NKV_LeafStep.project_source
#print NKV_LeafStep.source
#print axioms NKV_LeafStep.source
#print NKV_LeafTotal.reset
#print axioms NKV_LeafTotal.reset
#print NKV_LeafTotal.source
#print axioms NKV_LeafTotal.source
#print NKV_LeafTraversal.source
#print axioms NKV_LeafTraversal.source
#print NKV_LoopTransport.erase_flow
#print axioms NKV_LoopTransport.erase_flow
#print NKV_LoopTransport.execute
#print axioms NKV_LoopTransport.execute
#print NKV_LoopTransport.source
#print axioms NKV_LoopTransport.source
#print NKV_LoopTransport.transport
#print axioms NKV_LoopTransport.transport
#print NKV_OkTransport.batch
#print axioms NKV_OkTransport.batch
#print NKV_OkTransport.parent_observation
#print axioms NKV_OkTransport.parent_observation
#print NKV_OkTransport.tree
#print axioms NKV_OkTransport.tree
#print NKV_OkTransport.tree_observation
#print axioms NKV_OkTransport.tree_observation
#print NKV_OkTransport.values
#print axioms NKV_OkTransport.values
#print NKV_OuterSource.bind_observed
#print axioms NKV_OuterSource.bind_observed
#print NKV_OuterSource.concrete
#print axioms NKV_OuterSource.concrete
#print NKV_OuterSource.source
#print axioms NKV_OuterSource.source
#print NKV_OuterSource.values_concrete
#print axioms NKV_OuterSource.values_concrete
#print NKV_OuterTotal.batch
#print axioms NKV_OuterTotal.batch
#print NKV_OuterTotal.bind_roots
#print axioms NKV_OuterTotal.bind_roots
#print NKV_PaddingChunks.scan
#print axioms NKV_PaddingChunks.scan
#print NKV_PaddingChunks.total
#print axioms NKV_PaddingChunks.total
#print NKV_PaddingInstall.any_congr
#print axioms NKV_PaddingInstall.any_congr
#print NKV_PaddingInstall.callback
#print axioms NKV_PaddingInstall.callback
#print NKV_PaddingInstall.total
#print axioms NKV_PaddingInstall.total
#print NKV_PaddingValue.source
#print axioms NKV_PaddingValue.source
#print NKV_ParentSource.next_congr
#print axioms NKV_ParentSource.next_congr
#print NKV_ParentSource.next_observed
#print axioms NKV_ParentSource.next_observed
#print NKV_ParentSource.next_question
#print axioms NKV_ParentSource.next_question
#print NKV_ParentSource.three_congr
#print axioms NKV_ParentSource.three_congr
#print NKV_ParentSource.three_next
#print axioms NKV_ParentSource.three_next
#print NKV_ParentSource.values
#print axioms NKV_ParentSource.values
#print NKV_ParentTotal.read
#print axioms NKV_ParentTotal.read
#print NKV_ParentTotal.three
#print axioms NKV_ParentTotal.three
#print NKV_ParentTotal.values
#print axioms NKV_ParentTotal.values
#print NKV_ParentTrace.first_error
#print axioms NKV_ParentTrace.first_error
#print NKV_ParentTrace.next_congr
#print axioms NKV_ParentTrace.next_congr
#print NKV_ParentTrace.next_observed
#print axioms NKV_ParentTrace.next_observed
#print NKV_ParentTrace.second_error
#print axioms NKV_ParentTrace.second_error
#print NKV_ParentTrace.three_congr
#print axioms NKV_ParentTrace.three_congr
#print NKV_ProducerDomain.caller
#print axioms NKV_ProducerDomain.caller
#print NKV_ProducerDomain.tx1_count
#print axioms NKV_ProducerDomain.tx1_count
#print NKV_ProducerDomain.tx2_bytes
#print axioms NKV_ProducerDomain.tx2_bytes
#print NKV_Progress.continues
#print axioms NKV_Progress.continues
#print NKV_Progress.done_classified
#print axioms NKV_Progress.done_classified
#print NKV_QueryPlan.slot_history
#print axioms NKV_QueryPlan.slot_history
#print NKV_QueryPlan.tail_history
#print axioms NKV_QueryPlan.tail_history
#print NKV_ReturnBoundary.duplicate_preserved
#print axioms NKV_ReturnBoundary.duplicate_preserved
#print NKV_ReturnBoundary.lost
#print axioms NKV_ReturnBoundary.lost
#print NKV_ReturnBoundary.observed
#print axioms NKV_ReturnBoundary.observed
#print NKV_ReturnBoundary.prefix_transport
#print axioms NKV_ReturnBoundary.prefix_transport
#print NKV_ReturnBoundary.preserved
#print axioms NKV_ReturnBoundary.preserved
#print NKV_SlotInvocation.capacity
#print axioms NKV_SlotInvocation.capacity
#print NKV_SlotInvocation.physical
#print axioms NKV_SlotInvocation.physical
#print NKV_StepErasure.map_bind
#print axioms NKV_StepErasure.map_bind
#print NKV_StepErasure.map_cf
#print axioms NKV_StepErasure.map_cf
#print NKV_StepErasure.map_ite
#print axioms NKV_StepErasure.map_ite
#print NKV_StepErasure.map_ok
#print axioms NKV_StepErasure.map_ok
#print NKV_StepErasure.map_pair
#print axioms NKV_StepErasure.map_pair
#print NKV_StepErasure.source
#print axioms NKV_StepErasure.source
#print NKV_TailArithmetic.checked_scale
#print axioms NKV_TailArithmetic.checked_scale
#print NKV_TailArithmetic.fits
#print axioms NKV_TailArithmetic.fits
#print NKV_TailArithmetic.scaled_value
#print axioms NKV_TailArithmetic.scaled_value
#print NKV_TailContinue.source
#print axioms NKV_TailContinue.source
#print NKV_TailLoop.source
#print axioms NKV_TailLoop.source
#print NKV_TailModel.source
#print axioms NKV_TailModel.source
#print NKV_TailModel.verify
#print axioms NKV_TailModel.verify
#print NKV_TailProgram.source
#print axioms NKV_TailProgram.source
#print NKV_TailReject.capacity
#print axioms NKV_TailReject.capacity
#print NKV_TailReject.missing
#print axioms NKV_TailReject.missing
#print NKV_TailTotal.body
#print axioms NKV_TailTotal.body
#print NKV_TailTotal.loop
#print axioms NKV_TailTotal.loop
#print NKV_TraceCases.all_ok
#print axioms NKV_TraceCases.all_ok
#print NKV_TraceCases.first_abort
#print axioms NKV_TraceCases.first_abort
#print NKV_TraceCases.second_abort
#print axioms NKV_TraceCases.second_abort
#print NKV_TraceCases.third_abort
#print axioms NKV_TraceCases.third_abort
#print NKV_TraceCases.third_error
#print axioms NKV_TraceCases.third_error
#print NKV_TreeBuild.source
#print axioms NKV_TreeBuild.source
#print NKV_TreeEntry.source
#print axioms NKV_TreeEntry.source
#print NKV_TreeErrors.classified
#print axioms NKV_TreeErrors.classified
#print NKV_TreeErrors.complete
#print axioms NKV_TreeErrors.complete
#print NKV_TreeErrors.error_iff
#print axioms NKV_TreeErrors.error_iff
#print NKV_TreeErrors.returned_allowed
#print axioms NKV_TreeErrors.returned_allowed
#print NKV_TreeModel.source
#print axioms NKV_TreeModel.source
#print NKV_TreeSource.bind_observed
#print axioms NKV_TreeSource.bind_observed
#print NKV_TreeSource.boundary
#print axioms NKV_TreeSource.boundary
#print NKV_TreeSource.loop_observed
#print axioms NKV_TreeSource.loop_observed
#print NKV_TreeSource.prefix_source
#print axioms NKV_TreeSource.prefix_source
#print NKV_TreeSource.source
#print axioms NKV_TreeSource.source
#print NKV_TreeSource.span0
#print axioms NKV_TreeSource.span0
#print NKV_TreeSource.span1
#print axioms NKV_TreeSource.span1
#print NKV_TreeTotal.source
#print axioms NKV_TreeTotal.source
#print NKV_VerifyInvocation.returning
#print axioms NKV_VerifyInvocation.returning
#print NKV_VerifyInvocation.tx2
#print axioms NKV_VerifyInvocation.tx2
