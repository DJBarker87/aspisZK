import NBN_AccountCallbackObstruction
import NBN_AfterDecode00
import NBN_AfterDecode04
import NBN_AfterDecode08
import NBN_AfterDecode12
import NBN_AfterDecode16
import NBN_AfterDecodeParent
import NBN_AfterDecodeTypes
import NBN_AfterstateDecoderDependency
import NBN_ArrayNe
import NBN_BindingChecks
import NBN_CallbackObstruction
import NBN_ControlObservations
import NBN_DigestResultDependency
import NBN_EncoderBytes
import NBN_EncoderContents
import NBN_EncoderDomains
import NBN_EncoderObservation
import NBN_EncoderRejection
import NBN_EncoderResult
import NBN_EncoderSummary
import NBN_FirstByteDependency
import NBN_FrontierDependency
import NBN_InstalledChildren
import NBN_InstalledEncoder
import NBN_IteratorAssociation
import NBN_LateFactor
import NBN_LateInvariant
import NBN_LatePrepare
import NBN_LateResult
import NBN_LateSummary
import NBN_LateTail
import NBN_OutputLane
import NBN_ResultDependency
import NBN_ResultValidator
import NBN_StatementCut
import NBN_StatementDomains
import NBN_StatementEncoderSummary
import NBN_StatementResult
import NBN_U03
import NBN_U04
import NBN_U05
import NBN_ValidatorDomains
import NBN_ValidatorSummary
import NBN_WordArrayEq
set_option autoImplicit false

#print axioms NBN_AccountCallbackObstruction.master_unconstrained
#print axioms NBN_AccountCallbackObstruction.checkpoint_unconstrained
#print axioms NBN_AccountCallbackObstruction.request_unconstrained
#print axioms NBN_AfterDecode00.source
#print axioms NBN_AfterDecode04.source
#print axioms NBN_AfterDecode08.source
#print axioms NBN_AfterDecode12.source
#print axioms NBN_AfterDecode16.source
#print axioms NBN_AfterDecodeParent.source
#print axioms NBN_AfterstateDecoderDependency.source
#print axioms NBN_ArrayNe.bytes
#print axioms NBN_ArrayNe.words
#print axioms NBN_BindingChecks.factor
#print axioms NBN_BindingChecks.fields
#print axioms NBN_CallbackObstruction.registry_unconstrained
#print axioms NBN_CallbackObstruction.no_fixed_registry_law
#print axioms NBN_ControlObservations.payment_bytes
#print axioms NBN_ControlObservations.payment_error_stops
#print axioms NBN_ControlObservations.lane_error_stops
#print axioms NBN_DigestResultDependency.fold_exact
#print axioms NBN_DigestResultDependency.live_model
#print axioms NBN_DigestResultDependency.after_model
#print axioms NBN_DigestResultDependency.live_caller
#print axioms NBN_DigestResultDependency.after_caller
#print axioms NBN_EncoderBytes.length
#print axioms NBN_EncoderContents.private_contents
#print axioms NBN_EncoderContents.withdrawal_contents
#print axioms NBN_EncoderDomains.late
#print axioms NBN_EncoderDomains.transfer
#print axioms NBN_EncoderDomains.withdrawal
#print axioms NBN_EncoderDomains.validator
#print axioms NBN_EncoderObservation.faithful
#print axioms NBN_EncoderObservation.width
#print axioms NBN_EncoderRejection.source
#print axioms NBN_EncoderResult.source
#print axioms NBN_EncoderSummary.after_header
#print axioms NBN_EncoderSummary.live_header
#print axioms NBN_EncoderSummary.after_source
#print axioms NBN_EncoderSummary.live_source
#print axioms NBN_FirstByteDependency.first_source
#print axioms NBN_FirstByteDependency.lane_source
#print axioms NBN_FrontierDependency.live_fold
#print axioms NBN_FrontierDependency.after_fold
#print axioms NBN_FrontierDependency.rows_canonical
#print axioms NBN_FrontierDependency.live_caller
#print axioms NBN_FrontierDependency.after_caller
#print axioms NBN_InstalledChildren.validator
#print axioms NBN_InstalledChildren.late
#print axioms NBN_InstalledEncoder.source
#print axioms NBN_IteratorAssociation.next_row
#print axioms NBN_IteratorAssociation.exhausted
#print axioms NBN_LateFactor.bind_ext
#print axioms NBN_LateFactor.raw_eq
#print axioms NBN_LateInvariant.value_length
#print axioms NBN_LateInvariant.ready
#print axioms NBN_LateInvariant.statement_ready
#print axioms NBN_LatePrepare.exact
#print axioms NBN_LateResult.factor
#print axioms NBN_LateResult.header_length
#print axioms NBN_LateResult.source
#print axioms NBN_LateSummary.tail_source
#print axioms NBN_LateSummary.source
#print axioms NBN_OutputLane.first_source
#print axioms NBN_OutputLane.source
#print axioms NBN_ResultDependency.source
#print axioms NBN_ResultValidator.source
#print axioms NBN_StatementCut.source
#print axioms NBN_StatementCut.lower_substitution
#print axioms NBN_StatementDomains.payment_reached
#print axioms NBN_StatementDomains.bindings
#print axioms NBN_StatementDomains.lane_late
#print axioms NBN_StatementDomains.late_children
#print axioms NBN_StatementEncoderSummary.prefix_source
#print axioms NBN_StatementEncoderSummary.source
#print axioms NBN_StatementResult.source
#print axioms NBN_U03.conditional
#print axioms NBN_U04.conditional_helpers
#print axioms NBN_U05.conditional
#print axioms NBN_U05.validator_nullifier
#print axioms NBN_U05.encoder_kind
#print axioms NBN_ValidatorDomains.afterstate
#print axioms NBN_ValidatorDomains.live
#print axioms NBN_ValidatorDomains.after_row
#print axioms NBN_ValidatorDomains.live_row
#print axioms NBN_ValidatorSummary.payment_source
#print axioms NBN_ValidatorSummary.chain_pure
#print axioms NBN_ValidatorSummary.tail_source
#print axioms NBN_ValidatorSummary.source
#print axioms NBN_WordArrayEq.list_eq
#print axioms NBN_WordArrayEq.source
