import R1Z.PV_RJDec_CommonCases
import PV_DIAG2_Effects
import PV_DIAG3_Execution
import PV_RJ4IDB_Channels
import PV_RJ4IDB_Decoder
import PV_RJ4IDB_DiagAdapter
import PV_RJ4IDB_PowersControl
import PV_RJ4IDB_PowersBridge
import PV_RJ4IDB_Op254
import PV_RJ4IDB_TraceBind
import PV_RJ4IDB_ClientSuffix
import PV_RJ4IDB_CallerPublic
import PV_RJ4IDB_SourceTrace
import PV_RJ4IDB_ResultChannels
import PV_RJ4IDB_DecoderCases
import PV_RJ4IDB_FieldQ
import PV_RJ4IDB_FieldR
import PV_RJ4IDB_FieldQMul
import PV_RJ4IDB_FieldWide
import PV_RJ4IDB_NativePowers
import PV_RJ4IDB_Diag2Adapter
import PV_RJ4IDB_Publication
import PV_RJ4IDB_ChannelFibres
import PV_RJ4IDB_Extensions
import PV_RJ4IDB_PowersSafety
import PV_RJ4IDB_PowersTotal
import PV_RJ4IDB_NativeTrace
import PV_RJ4IDB_NativeChannels
import PV_RJ4IDB_NativeFactor
import JHb_DataMaster
import JHg_DataMaster
import JHb_DataForest
import JHg_DataForest
import JHb_DataLane
import JHb_DataRegistry
import JHb_DataEntry
import PV_2TNV_WorldData
import PV_RJ4IDB_ResultOutput
import PV_RJ4IDB_ResultOutputCases
import PV_RJ4IDB_ByteWindow
import PV_DIAG3_Ownership
import PV_DIAG3_Write
import PV_DIAG3_Formatter
import PV_DIAG3_Syswrite
import PV_DIAG3_Drop
import PV_DIAG3_Reporting
import PV_DIAG3_Capture
import PV_DIAG3_Joint
import PV_DIAG3_Client
import PV_DIAG3_Observer
import PV_DIAG2_Retry
import PV_DIAG2_Exit
import PV_DIAG2_ErrorText
import PV_DIAG2_MaskMapper
import PV_DIAG2_Rejection
import PV_DIAG2_Exhaustion
import PV_RJ4IDB_CallerLive
import PV_RJ4IDB_StdIndex
import PV_RJ4IDB_DiagWorld
import PV_RJ4IDB_ClientTrace
import PV_RJ4IDB_ClientAbnormal
import PV_RJ4IDB_DiagUnitText
import PV_RJ4IDB_DiagSyswrite
import PV_DIAG2_ClientRetry
import PV_DIAG2_ApiSink
import PV_RJ4IDB_DiagJoint
import PV_RJ4IDB_ErrorOccurrence
import PV_RJ4IDB_NativeConstants
import PV_RJ4IDB_CallerSemantic
import PV_RJ4IDB_OpenInputs
/-! Complete checked types; native producer inputs remain OPEN Props, not instances. -/
#check PV_RJ4IDB.files_append
#check PV_RJ4IDB.decoder_injective
#check PV_RJ4IDB.failure_prefix
#check PV_RJ4IDB.divergence_prefix
#check PV_RJ4IDB.panic_prefix
#check PV_RJ4IDB.abort_prefix
#check PV_RJ4IDB.diag_events
#check PV_RJ4IDB.diag_prefix
#check PV_RJ4IDB.diag_bind_abort
#check PV_RJ4IDB.diag_bind_diverge
#check R1Z.PV_RJ4IDB_PowersControl.source_unfold
#check R1Z.PV_RJ4IDB_PowersControl.dispatch_congr
#check R1Z.PV_RJ4IDB_PowersControl.loop_finite
#check R1Z.PV_RJ4IDB_PowersControl.source
#check R1Z.PV_RJ4IDB_PowersBridge.step
#check R1Z.PV_RJ4IDB_PowersBridge.finite
#check R1Z.PV_RJ4IDB_PowersBridge.complete
#check R1Z.PV_RJ4IDB_Op254.entry
#check R1Z.PV_RJ4IDB_Op254.installation
#check PV_RJ4IDB.bind_prepend
#check PV_RJ4IDB.bind_assoc
#check PV_RJ4IDB.bind_failure
#check PV_RJ4IDB.bind_divergence
#check PV_RJ4IDB.main_order
#check PV_RJ4IDB.statement_failure_preserves_proof
#check PV_RJ4IDB.json_divergence_preserves_files
#check R1Z.PV_RJ4IDB_CallerPublic.request_public_eq
#check R1Z.PV_RJ4IDB_CallerPublic.caller_statement_eq
#check R1Z.PV_RJ4IDB_CallerPublic.caller_fibre
#check PV_RJ4IDB.actual_factors
#check PV_RJ4IDB.result_fibres_exact
#check PV_RJ4IDB.returned_component
#check PV_RJ4IDB.returned_success
#check PV_RJ4IDB.returned_failure
#check PV_RJ4IDB.returned_divergence
#check PV_RJ4IDB.trace_component_fibres
#check PV_RJ4IDB.disclosed_ok
#check PV_RJ4IDB.disclosed_fail
#check PV_RJ4IDB.disclosed_div
#check PV_RJ4IDB.oracle_ok
#check PV_RJ4IDB.oracle_fail
#check PV_RJ4IDB.oracle_div
#check R1Z.PV_RJ4IDB_FieldQ.add
#check R1Z.PV_RJ4IDB_FieldQ.sub
#check R1Z.PV_RJ4IDB_FieldR.complete
#check R1Z.PV_RJ4IDB_FieldQMul.complete
#check R1Z.PV_RJ4IDB_FieldWide.mulU_complete
#check R1Z.PV_RJ4IDB_FieldWide.complete
#check R1Z.PV_RJ4IDB_NativePowers.primitives_equal
#check R1Z.PV_RJ4IDB_NativePowers.deployed_callback
#check R1Z.PV_RJ4IDB_NativePowers.deployed_installation
#check PV_RJ4IDB.diag2_recover
#check PV_RJ4IDB.diag2_failure_recover
#check PV_RJ4IDB.diag2_divergence_recover
#check PV_RJ4IDB.diag2_append
#check PV_RJ4IDB.proof_statement_order
#check PV_RJ4IDB.publication_append_prefix
#check PV_RJ4IDB.available_result_component
#check PV_RJ4IDB.projection_law
#check PV_RJ4IDB.product_law
#check PV_RJ4IDB.result_decoder_exists_iff
#check PV_RJ4IDB.component_cases
#check R1Z.PV_RJ4IDB_PowersSafety.increment
#check R1Z.PV_RJ4IDB_PowersSafety.index_restore
#check R1Z.PV_RJ4IDB_PowersSafety.mul_total
#check R1Z.PV_RJ4IDB_PowersSafety.finite_total
#check R1Z.PV_RJ4IDB_PowersTotal.complete
#check R1Z.PV_RJ4IDB_PowersTotal.no_fail
#check R1Z.PV_RJ4IDB_PowersTotal.no_diverge
#check PV_RJ4IDB.nativeFiles_translation
#check PV_RJ4IDB.nativeJSON_translation
#check PV_RJ4IDB.nativeStdout_translation
#check PV_RJ4IDB.nativeDiag2_translation
#check PV_RJ4IDB.nativeDiag3_translation
#check PV_RJ4IDB.nativeCounts_translation
#check PV_RJ4IDB.nativeTimes_translation
#check PV_RJ4IDB.nativeOracle_translation
#check PV_RJ4IDB.nativeRejections_translation
#check PV_RJ4IDB.nativeSide_translation
#check PV_RJ4IDB.native_factorization
#check PV_RJ4IDB.success_factorization
#check PV_RJ4IDB.failure_factorization
#check PV_RJ4IDB.divergence_factorization
#check PV_RJ4IDB.panic_factorization
#check PV_RJ4IDB.abort_factorization
#check PV_RJ4IDB.all_prefixes
#check PV_RJ4IDB.resultOutput_map
#check PV_RJ4IDB.count_retained
#check PV_RJ4IDB.returned_output_fibres
#check PV_RJ4IDB.output_disclosed_ok
#check PV_RJ4IDB.output_disclosed_fail
#check PV_RJ4IDB.output_disclosed_div
#check PV_RJ4IDB.output_oracle_ok
#check PV_RJ4IDB.output_oracle_fail
#check PV_RJ4IDB.output_oracle_div
#check R1Z.PV_RJ4IDB_ByteWindow.word_window
#check R1Z.PV_RJ4IDB_ByteWindow.digest_window
#check R1Z.PV_RJ4IDB_CallerLive.live_index
#check R1Z.PV_RJ4IDB_CallerLive.live_frontier
#check R1Z.PV_RJ4IDB_CallerLive.live_public_eq
#check R1Z.PV_RJ4IDB_CallerLive.caller_to_transfer13
#check R1Z.PV_RJ4IDB_CallerLive.caller_witness
#check R1Z.PV_RJ4IDB_StdIndex.source_equal
#check R1Z.PV_RJ4IDB_StdIndex.in_bounds
#check R1Z.PV_RJ4IDB_StdIndex.out_of_bounds
#check PV_RJ4IDB.diag_with_state_order
#check PV_RJ4IDB.final_state_abort
#check PV_RJ4IDB.final_state_divergence
#check PV_RJ4IDB.native_normal_model
#check PV_RJ4IDB.result_and_trace
#check PV_RJ4IDB.abort_preserved
#check PV_RJ4IDB.divergence_preserved
#check PV_RJ4IDB.panic_preserved
#check PV_RJ4IDB.failed_handler
#check PV_RJ4IDB.divergent_handler
#check PV_RJ4IDB.unit_variant_content
#check PV_RJ4IDB.unit_content_retained
#check PV_RJ4IDB.stderr_source
#check PV_RJ4IDB.stderr_abort_prefix
#check PV_RJ4IDB.stderr_divergent_prefix
#check PV_RJ4IDB.coupled_decoder
#check PV_RJ4IDB.coupled_continuation_decoder
#check PV_RJ4IDB.output_stop_iff
#check PV_RJ4IDB.reject_free_output
#check PV_RJ4IDB.client_no_rejected_output
#check R1Z.PV_RJ4IDB_NativeConstants.zero_source
#check R1Z.PV_RJ4IDB_NativeConstants.one_source
#check R1Z.PV_RJ4IDB_NativeConstants.deployed29_total
#check R1Z.PV_RJ4IDB_CallerSemantic.typed_projection
#check R1Z.PV_RJ4IDB_CallerSemantic.caller_to_transfer13
#check R1Z.PV_RJ4IDB_CallerSemantic.consume
#check PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
#check PV_RJ4IDB.OpenInputs.RUNJOIN_STATEMENT_BYTES
#check PV_RJ4IDB.OpenInputs.DIAG_FILE_TRACE
#check PV_RJ4IDB.OpenInputs.DIAG_JSON_STDOUT_TRACE
#check PV_RJ4IDB.OpenInputs.DIAG_ERROR_STDERR_TRACE
#check PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE
#check PV_RJ4IDB.OpenInputs.L1_TIME_TRACE
#check PV_RJ4IDB.OpenInputs.L1_ORACLE_PREFIX
#check PV_RJ4IDB.OpenInputs.L1_RETAINED_SIDECHANNELS
#check R1Z.PV_RJDec_CommonCases.complete_pair
#check R1Z.PV_RJDec_ResultCases.fibres_iff
#check R1Z.PV_RJDec_V047Native.consume
#check R1Z.PV_RJ4IDB_NativePowers.deployed_installation
#check R1Z.PV_RJ4IDB_CallerSemantic.caller_to_transfer13
#check R1Z.PV_RJ4IDB_CallerSemantic.consume
#check PV_RJ4IDB.native_factorization
#check PV_RJ4IDB.all_prefixes
#check PV_RJ4IDB.result_fibres_exact

/-! Combined corrected full-statement and every-theorem axioms audit. -/
#print axioms PV_RJ4IDB.files_append
#print axioms PV_RJ4IDB.decoder_injective
#print axioms PV_RJ4IDB.failure_prefix
#print axioms PV_RJ4IDB.divergence_prefix
#print axioms PV_RJ4IDB.panic_prefix
#print axioms PV_RJ4IDB.abort_prefix
#print axioms PV_RJ4IDB.diag_events
#print axioms PV_RJ4IDB.diag_prefix
#print axioms PV_RJ4IDB.diag_bind_abort
#print axioms PV_RJ4IDB.diag_bind_diverge
#print axioms R1Z.PV_RJ4IDB_PowersControl.source_unfold
#print axioms R1Z.PV_RJ4IDB_PowersControl.dispatch_congr
#print axioms R1Z.PV_RJ4IDB_PowersControl.loop_finite
#print axioms R1Z.PV_RJ4IDB_PowersControl.source
#print axioms R1Z.PV_RJ4IDB_PowersBridge.step
#print axioms R1Z.PV_RJ4IDB_PowersBridge.finite
#print axioms R1Z.PV_RJ4IDB_PowersBridge.complete
#print axioms R1Z.PV_RJ4IDB_Op254.entry
#print axioms R1Z.PV_RJ4IDB_Op254.installation
#print axioms PV_RJ4IDB.bind_prepend
#print axioms PV_RJ4IDB.bind_assoc
#print axioms PV_RJ4IDB.bind_failure
#print axioms PV_RJ4IDB.bind_divergence
#print axioms PV_RJ4IDB.main_order
#print axioms PV_RJ4IDB.statement_failure_preserves_proof
#print axioms PV_RJ4IDB.json_divergence_preserves_files
#print axioms R1Z.PV_RJ4IDB_CallerPublic.request_public_eq
#print axioms R1Z.PV_RJ4IDB_CallerPublic.caller_statement_eq
#print axioms R1Z.PV_RJ4IDB_CallerPublic.caller_fibre
#print axioms PV_RJ4IDB.actual_factors
#print axioms PV_RJ4IDB.result_fibres_exact
#print axioms PV_RJ4IDB.returned_component
#print axioms PV_RJ4IDB.returned_success
#print axioms PV_RJ4IDB.returned_failure
#print axioms PV_RJ4IDB.returned_divergence
#print axioms PV_RJ4IDB.trace_component_fibres
#print axioms PV_RJ4IDB.disclosed_ok
#print axioms PV_RJ4IDB.disclosed_fail
#print axioms PV_RJ4IDB.disclosed_div
#print axioms PV_RJ4IDB.oracle_ok
#print axioms PV_RJ4IDB.oracle_fail
#print axioms PV_RJ4IDB.oracle_div
#print axioms R1Z.PV_RJ4IDB_FieldQ.add
#print axioms R1Z.PV_RJ4IDB_FieldQ.sub
#print axioms R1Z.PV_RJ4IDB_FieldR.complete
#print axioms R1Z.PV_RJ4IDB_FieldQMul.complete
#print axioms R1Z.PV_RJ4IDB_FieldWide.mulU_complete
#print axioms R1Z.PV_RJ4IDB_FieldWide.complete
#print axioms R1Z.PV_RJ4IDB_NativePowers.primitives_equal
#print axioms R1Z.PV_RJ4IDB_NativePowers.deployed_callback
#print axioms R1Z.PV_RJ4IDB_NativePowers.deployed_installation
#print axioms PV_RJ4IDB.diag2_recover
#print axioms PV_RJ4IDB.diag2_failure_recover
#print axioms PV_RJ4IDB.diag2_divergence_recover
#print axioms PV_RJ4IDB.diag2_append
#print axioms PV_RJ4IDB.proof_statement_order
#print axioms PV_RJ4IDB.publication_append_prefix
#print axioms PV_RJ4IDB.available_result_component
#print axioms PV_RJ4IDB.projection_law
#print axioms PV_RJ4IDB.product_law
#print axioms PV_RJ4IDB.result_decoder_exists_iff
#print axioms PV_RJ4IDB.component_cases
#print axioms R1Z.PV_RJ4IDB_PowersSafety.increment
#print axioms R1Z.PV_RJ4IDB_PowersSafety.index_restore
#print axioms R1Z.PV_RJ4IDB_PowersSafety.mul_total
#print axioms R1Z.PV_RJ4IDB_PowersSafety.finite_total
#print axioms R1Z.PV_RJ4IDB_PowersTotal.complete
#print axioms R1Z.PV_RJ4IDB_PowersTotal.no_fail
#print axioms R1Z.PV_RJ4IDB_PowersTotal.no_diverge
#print axioms PV_RJ4IDB.nativeFiles_translation
#print axioms PV_RJ4IDB.nativeJSON_translation
#print axioms PV_RJ4IDB.nativeStdout_translation
#print axioms PV_RJ4IDB.nativeDiag2_translation
#print axioms PV_RJ4IDB.nativeDiag3_translation
#print axioms PV_RJ4IDB.nativeCounts_translation
#print axioms PV_RJ4IDB.nativeTimes_translation
#print axioms PV_RJ4IDB.nativeOracle_translation
#print axioms PV_RJ4IDB.nativeRejections_translation
#print axioms PV_RJ4IDB.nativeSide_translation
#print axioms PV_RJ4IDB.native_factorization
#print axioms PV_RJ4IDB.success_factorization
#print axioms PV_RJ4IDB.failure_factorization
#print axioms PV_RJ4IDB.divergence_factorization
#print axioms PV_RJ4IDB.panic_factorization
#print axioms PV_RJ4IDB.abort_factorization
#print axioms PV_RJ4IDB.all_prefixes
#print axioms PV_RJ4IDB.resultOutput_map
#print axioms PV_RJ4IDB.count_retained
#print axioms PV_RJ4IDB.returned_output_fibres
#print axioms PV_RJ4IDB.output_disclosed_ok
#print axioms PV_RJ4IDB.output_disclosed_fail
#print axioms PV_RJ4IDB.output_disclosed_div
#print axioms PV_RJ4IDB.output_oracle_ok
#print axioms PV_RJ4IDB.output_oracle_fail
#print axioms PV_RJ4IDB.output_oracle_div
#print axioms R1Z.PV_RJ4IDB_ByteWindow.word_window
#print axioms R1Z.PV_RJ4IDB_ByteWindow.digest_window
#print axioms R1Z.PV_RJ4IDB_CallerLive.live_index
#print axioms R1Z.PV_RJ4IDB_CallerLive.live_frontier
#print axioms R1Z.PV_RJ4IDB_CallerLive.live_public_eq
#print axioms R1Z.PV_RJ4IDB_CallerLive.caller_to_transfer13
#print axioms R1Z.PV_RJ4IDB_CallerLive.caller_witness
#print axioms R1Z.PV_RJ4IDB_StdIndex.source_equal
#print axioms R1Z.PV_RJ4IDB_StdIndex.in_bounds
#print axioms R1Z.PV_RJ4IDB_StdIndex.out_of_bounds
#print axioms PV_RJ4IDB.diag_with_state_order
#print axioms PV_RJ4IDB.final_state_abort
#print axioms PV_RJ4IDB.final_state_divergence
#print axioms PV_RJ4IDB.native_normal_model
#print axioms PV_RJ4IDB.result_and_trace
#print axioms PV_RJ4IDB.abort_preserved
#print axioms PV_RJ4IDB.divergence_preserved
#print axioms PV_RJ4IDB.panic_preserved
#print axioms PV_RJ4IDB.failed_handler
#print axioms PV_RJ4IDB.divergent_handler
#print axioms PV_RJ4IDB.unit_variant_content
#print axioms PV_RJ4IDB.unit_content_retained
#print axioms PV_RJ4IDB.stderr_source
#print axioms PV_RJ4IDB.stderr_abort_prefix
#print axioms PV_RJ4IDB.stderr_divergent_prefix
#print axioms PV_RJ4IDB.coupled_decoder
#print axioms PV_RJ4IDB.coupled_continuation_decoder
#print axioms PV_RJ4IDB.output_stop_iff
#print axioms PV_RJ4IDB.reject_free_output
#print axioms PV_RJ4IDB.client_no_rejected_output
#print axioms R1Z.PV_RJ4IDB_NativeConstants.zero_source
#print axioms R1Z.PV_RJ4IDB_NativeConstants.one_source
#print axioms R1Z.PV_RJ4IDB_NativeConstants.deployed29_total
#print axioms R1Z.PV_RJ4IDB_CallerSemantic.typed_projection
#print axioms R1Z.PV_RJ4IDB_CallerSemantic.caller_to_transfer13
#print axioms R1Z.PV_RJ4IDB_CallerSemantic.consume
#print axioms PV_RJ4IDB.OpenInputs.RUNJOIN_PUBLISH_COMPACT
#print axioms PV_RJ4IDB.OpenInputs.RUNJOIN_STATEMENT_BYTES
#print axioms PV_RJ4IDB.OpenInputs.DIAG_FILE_TRACE
#print axioms PV_RJ4IDB.OpenInputs.DIAG_JSON_STDOUT_TRACE
#print axioms PV_RJ4IDB.OpenInputs.DIAG_ERROR_STDERR_TRACE
#print axioms PV_RJ4IDB.OpenInputs.L1_COUNT_TRACE
#print axioms PV_RJ4IDB.OpenInputs.L1_TIME_TRACE
#print axioms PV_RJ4IDB.OpenInputs.L1_ORACLE_PREFIX
#print axioms PV_RJ4IDB.OpenInputs.L1_RETAINED_SIDECHANNELS
#print axioms R1Z.PV_RJDec_CommonCases.complete_pair
#print axioms R1Z.PV_RJDec_ResultCases.fibres_iff
#print axioms R1Z.PV_RJDec_V047Native.consume
