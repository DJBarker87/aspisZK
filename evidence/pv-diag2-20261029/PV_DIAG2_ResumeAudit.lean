import PV_DIAG2_AnyhowDebugControl
import PV_DIAG2_ApiSink
import PV_DIAG2_BacktraceFlags
import PV_DIAG2_CaptureControl
import PV_DIAG2_ClientRetry
import PV_DIAG2_ComposeSinks
import PV_DIAG2_Effects
import PV_DIAG2_ErrorText
import PV_DIAG2_Exhaustion
import PV_DIAG2_Exit
import PV_DIAG2_LogControl
import PV_DIAG2_MaskMapper
import PV_DIAG2_PrintControl
import PV_DIAG2_Process
import PV_DIAG2_Rejection
import PV_DIAG2_Retry
import PV_DIAG2_ReturnFrames
import PV_DIAG2_SemanticMapper
import PV_DIAG2_Sinks
import PV_DIAG2_Termination
import PV_DIAG2_WireEquality
#print axioms PV_DIAG2.debug_alternate_only
#print axioms PV_DIAG2.debug_ordinary_sequence
#print axioms PV_DIAG2.debug_display_error_stops
#print axioms PV_DIAG2.debug_display_panic
#print axioms PV_DIAG2.debug_display_oom
#print axioms PV_DIAG2.debug_display_diverges
#print axioms PV_DIAG2.debug_not_captured
#print axioms PV_DIAG2.debug_captured_branch
#print axioms PV_DIAG2.debug_getter_panic
#print axioms PV_DIAG2.debug_captured_error_state
#print axioms PV_DIAG2.debug_captured_oom
#print axioms PV_DIAG2.reject_free_api
#print axioms PV_DIAG2.client_observed_api_not_rejected
#print axioms PV_DIAG2.finish_splits_prefix
#print axioms PV_DIAG2.rejected_not_in_report_suffix
#print axioms PV_DIAG2.lib_zero_suppresses
#print axioms PV_DIAG2.lib_nonzero_enables
#print axioms PV_DIAG2.absent_lib_falls_back
#print axioms PV_DIAG2.nonunicode_lib_falls_back
#print axioms PV_DIAG2.absent_back_disables
#print axioms PV_DIAG2.nonunicode_back_disables
#print axioms PV_DIAG2.zero_back_disables
#print axioms PV_DIAG2.initial_cache_request
#print axioms PV_DIAG2.cached_off_ignores_environment
#print axioms PV_DIAG2.cached_on_ignores_environment
#print axioms PV_DIAG2.cache_code_range
#print axioms PV_DIAG2.requested_store_range
#print axioms PV_DIAG2.public_enablement
#print axioms PV_DIAG2.unicode_lib_ignores_back
#print axioms PV_DIAG2.env_unicode_skips_fallback
#print axioms PV_DIAG2.env_absent_runs_fallback
#print axioms PV_DIAG2.env_nonunicode_runs_fallback
#print axioms PV_DIAG2.env_panic_retained
#print axioms PV_DIAG2.fallback_oom_scope_retained
#print axioms PV_DIAG2.cached_off_no_env
#print axioms PV_DIAG2.cached_on_no_env
#print axioms PV_DIAG2.disabled_no_create
#print axioms PV_DIAG2.enabled_keeps_create
#print axioms PV_DIAG2.force_capture_bypasses_env
#print axioms PV_DIAG2.client_entropy_not_rejected
#print axioms PV_DIAG2.client_attempt_reject_free
#print axioms PV_DIAG2.client_run_reject_free
#print axioms PV_DIAG2.source_client_no_rejected
#print axioms PV_DIAG2.sink_append
#print axioms PV_DIAG2.sink_prepend
#print axioms PV_DIAG2.sink_silence_composes
#print axioms PV_DIAG2.sink_joint_composition
#print axioms PV_DIAG2.result_equality_not_stderr_equality
#print axioms PV_DIAG2.result_equality_not_frame_equality
#print axioms PV_DIAG2.message_public
#print axioms PV_DIAG2.report_disabled
#print axioms PV_DIAG2.disabled_frames_irrelevant
#print axioms PV_DIAG2.success_report_silent
#print axioms PV_DIAG2.error_report_exact
#print axioms PV_DIAG2.bind_panic
#print axioms PV_DIAG2.bind_oom
#print axioms PV_DIAG2.prior_panic
#print axioms PV_DIAG2.native_debug_join
#print axioms PV_DIAG2.variant_debug_public
#print axioms PV_DIAG2.native_report_disabled
#print axioms PV_DIAG2.rejected_debug_literal
#print axioms PV_DIAG2.exhaustion_debug_literal
#print axioms PV_DIAG2.entropy_debug_literal
#print axioms PV_DIAG2.cap_requested_text
#print axioms PV_DIAG2.last_rejection_reports
#print axioms PV_DIAG2.cap_full_result
#print axioms PV_DIAG2.success_no_error_report
#print axioms PV_DIAG2.stopped_report
#print axioms PV_DIAG2.stopped_frames_disabled
#print axioms PV_DIAG2.exhaustion_requested_text
#print axioms PV_DIAG2.finish_result
#print axioms PV_DIAG2.final_source_result
#print axioms PV_DIAG2.log_static_guard_silent
#print axioms PV_DIAG2.log_runtime_off_skips_arguments
#print axioms PV_DIAG2.log_enabled_dispatch
#print axioms PV_DIAG2.log_level_panic
#print axioms PV_DIAG2.log_level_oom
#print axioms PV_DIAG2.log_load_panic
#print axioms PV_DIAG2.log_dispatch_panic
#print axioms PV_DIAG2.log_dispatch_oom
#print axioms PV_DIAG2.mask_mapper_exact
#print axioms PV_DIAG2.mask_mapper_silent
#print axioms PV_DIAG2.mask_branch_public
#print axioms PV_DIAG2.print_capture_suppresses_global
#print axioms PV_DIAG2.print_uncaptured_writes
#print axioms PV_DIAG2.print_write_ok
#print axioms PV_DIAG2.print_write_error
#print axioms PV_DIAG2.print_write_panics
#print axioms PV_DIAG2.print_write_oom
#print axioms PV_DIAG2.print_capture_panics
#print axioms PV_DIAG2.print_capture_oom
#print axioms PV_DIAG2.print_capture_diverges
#print axioms PV_DIAG2.print_write_diverges
#print axioms PV_DIAG2.process_retains_result
#print axioms PV_DIAG2.reporting_oom_retained
#print axioms PV_DIAG2.reporting_panic_retained
#print axioms PV_DIAG2.normal_report_request
#print axioms PV_DIAG2.active_pole_rejected
#print axioms PV_DIAG2.attempt_reject_free
#print axioms PV_DIAG2.run_reject_free
#print axioms PV_DIAG2.observed_reject_free
#print axioms PV_DIAG2.erase_run
#print axioms PV_DIAG2.rejected_effects
#print axioms PV_DIAG2.cap_no_direct_effects
#print axioms PV_DIAG2.fatal_effects_retained
#print axioms PV_DIAG2.source_retry_result
#print axioms PV_DIAG2.mask_exhaustion_rejected
#print axioms PV_DIAG2.report_spine
#print axioms PV_DIAG2.return_resumes_saved
#print axioms PV_DIAG2.returned_error_spine
#print axioms PV_DIAG2.proving_panic_keeps_frames
#print axioms PV_DIAG2.proving_oom_keeps_frames
#print axioms PV_DIAG2.active_comparison_no_payload
#print axioms PV_DIAG2.semantic_mapper_exact
#print axioms PV_DIAG2.semantic_mapper_silent
#print axioms PV_DIAG2.semantic_payload_irrelevant
#print axioms PV_DIAG2.retry_sink_exact
#print axioms PV_DIAG2.retry_sink_silent
#print axioms PV_DIAG2.sink_projection_retains_result
#print axioms PV_DIAG2.termination_success
#print axioms PV_DIAG2.captured_no_global
#print axioms PV_DIAG2.uncaptured_global
#print axioms PV_DIAG2.capture_panic
#print axioms PV_DIAG2.capture_oom
#print axioms PV_DIAG2.ignored_io_error
#print axioms PV_DIAG2.report_then_drop
#print axioms PV_DIAG2.report_panics_unwind
#print axioms PV_DIAG2.normal_error_exit
#print axioms PV_DIAG2.wire_equal_exact
#print axioms PV_DIAG2.active_pole_installed
