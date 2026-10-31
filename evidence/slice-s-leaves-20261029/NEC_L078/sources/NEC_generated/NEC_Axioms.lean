import NEC_Common
import NEC_Reference.Types
import NEC_Reference.Funs
import NEC_AfterstateBox
import NEC_AfterstateWindows
import NEC_LiveBox
import NEC_LaneBox
import NEC_PairRef.Types
import NEC_PairRef.Funs
import NEC_TransferDecode
import NEC_WithdrawalDecode
import NEC_ReplyRef.Types
import NEC_ReplyRef.Funs
import NEC_PureReplyAssociation
import NEC_LiveGeometry
import NEC_LiveConstants
import NEC_LiveReject
import NEC_Constructors
import NEC_LiveHeaderRef.Types
import NEC_StaticReplyTransport
import NEC_LiveHeaderRef.Funs
import NEC_ResultCaller
import NEC_SliceDomains
import NEC_ScalarPorts
import NEC_HeaderIndex
import NEC_Reconstruction
import NEC_PaymentDomains
import NEC_Widening
import NEC_EmitModel
import NEC_WrapperTotal
import NEC_HeaderPredicates
import NEC_HeaderMagic
import NEC_HeaderBinding0
import NEC_HeaderBinding1
import NEC_EmitRef.Types
import NEC_EmitRef.Funs
import NEC_BindingRef.Types
import NEC_BindingRef.Funs
import NEC_ReferenceLaws
import NEC_HeaderGuards
import NEC_HeaderBinding2
import NEC_HeaderBinding3
import NEC_ResultGeometry
import NEC_HeaderMonad
import NEC_HeaderJoin

#print axioms NEC_Common.caller_domain
#print axioms NEC_Common.reference_cohort
#print axioms NEC_Common.windows_transport
#print axioms NEC_AfterstateBox.emitted
#print axioms NEC_AfterstateBox.value_project
#print axioms NEC_AfterstateWindows.assemble
#print axioms NEC_AfterstateWindows.caller_domain
#print axioms NEC_LiveBox.emitted
#print axioms NEC_LiveBox.value_project
#print axioms NEC_LaneBox.emitted
#print axioms NEC_LaneBox.value_project
#print axioms NEC_TransferDecode.emitted
#print axioms NEC_TransferDecode.successful_fields
#print axioms NEC_TransferDecode.rejection
#print axioms NEC_WithdrawalDecode.emitted
#print axioms NEC_WithdrawalDecode.successful_fields
#print axioms NEC_WithdrawalDecode.rejection
#print axioms NEC_PureReplyAssociation.reference_equality
#print axioms NEC_PureReplyAssociation.emitted
#print axioms NEC_PureReplyAssociation.caller_domain
#print axioms NEC_LiveGeometry.current_root
#print axioms NEC_LiveGeometry.frontier_start
#print axioms NEC_LiveGeometry.byte_in_bounds
#print axioms NEC_LiveGeometry.window_length
#print axioms NEC_LiveGeometry.disjoint
#print axioms NEC_LiveGeometry.same_slot
#print axioms NEC_LiveGeometry.header_frame
#print axioms NEC_LiveConstants.binding_value
#print axioms NEC_LiveConstants.magic
#print axioms NEC_LiveConstants.version
#print axioms NEC_LiveConstants.live_width
#print axioms NEC_LiveConstants.late_width
#print axioms NEC_LiveConstants.after_width
#print axioms NEC_LiveReject.wrong_length
#print axioms NEC_Constructors.caller_domain
#print axioms NEC_Constructors.same_reply
#print axioms NEC_Constructors.transfer
#print axioms NEC_Constructors.withdrawal
#print axioms NEC_StaticReplyTransport.transport
#print axioms NEC_StaticReplyTransport.emitted_transport
#print axioms NEC_ResultCaller.caller_domain
#print axioms NEC_ResultCaller.fields
#print axioms NEC_ResultCaller.accepted
#print axioms NEC_ResultCaller.rejected
#print axioms NEC_SliceDomains.terminal_payment
#print axioms NEC_SliceDomains.request_payment
#print axioms NEC_SliceDomains.terminal_lane
#print axioms NEC_SliceDomains.terminal_anchor
#print axioms NEC_SliceDomains.live_child
#print axioms NEC_SliceDomains.after_child
#print axioms NEC_SliceDomains.terminal_common_minimum
#print axioms NEC_SliceDomains.result_after
#print axioms NEC_SliceDomains.scan_candidate
#print axioms NEC_SliceDomains.scan_proof
#print axioms NEC_SliceDomains.scan_tag
#print axioms NEC_SliceDomains.live_scalar_disjoint
#print axioms NEC_SliceDomains.common_payment_disjoint
#print axioms NEC_ScalarPorts.u32_natural_injective
#print axioms NEC_ScalarPorts.m31_natural_injective
#print axioms NEC_ScalarPorts.u64_natural_injective
#print axioms NEC_ScalarPorts.widened_word_injective
#print axioms NEC_HeaderIndex.index_read
#print axioms NEC_Reconstruction.caller_domain
#print axioms NEC_Reconstruction.common_domain
#print axioms NEC_Reconstruction.selected
#print axioms NEC_Reconstruction.gate
#print axioms NEC_PaymentDomains.transfer_caller
#print axioms NEC_PaymentDomains.withdrawal_caller
#print axioms NEC_Widening.u32_u64
#print axioms NEC_Widening.word_injective
#print axioms NEC_EmitModel.validation_error
#print axioms NEC_EmitModel.encode_error
#print axioms NEC_EmitModel.runtime_output
#print axioms NEC_EmitModel.bad_magic
#print axioms NEC_WrapperTotal.afterstate
#print axioms NEC_WrapperTotal.live
#print axioms NEC_WrapperTotal.lane
#print axioms NEC_WrapperTotal.transfer
#print axioms NEC_WrapperTotal.withdrawal
#print axioms NEC_HeaderPredicates.byte_spec
#print axioms NEC_HeaderMagic.emitted
#print axioms NEC_HeaderBinding0.emitted
#print axioms NEC_HeaderBinding1.emitted
#print axioms NEC_ReferenceLaws.emit_total
#print axioms NEC_ReferenceLaws.binding_total
#print axioms NEC_ReferenceLaws.runtime_projection
#print axioms NEC_HeaderGuards.guarded
#print axioms NEC_HeaderBinding2.emitted
#print axioms NEC_HeaderBinding3.emitted
#print axioms NEC_ResultGeometry.header
#print axioms NEC_ResultGeometry.copied_bounds
#print axioms NEC_ResultGeometry.copied_disjoint
#print axioms NEC_ResultGeometry.exact_afterstate_width
#print axioms NEC_ResultGeometry.arbitrary_byte
#print axioms NEC_HeaderMonad.ok_if
#print axioms NEC_HeaderJoin.emitted
