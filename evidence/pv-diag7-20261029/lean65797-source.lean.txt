import PV_DIAG7_Handoff
set_option autoImplicit false
namespace PV_DIAG7
open PV_DIAG3
/-- Audit the actual adopted public-input specialization: no stronger
same-coordinate source-independence premise is added. V400 remains the P
obligation needed to bind the native signal selection to this public input. -/
theorem DIAG_optionB_public_signal {W P C : Type}
 (pub : W → P) (coins : W → C) (publicSignal : P → C → Signal)
 (program : P → C → Nat → Program) (initial : P → C → State)
 (existingL1Count : P → C → Nat) (w u : W)
 (hp : pub w = pub u) (hc : coins w = coins u) :
 (fun n => DIAG_inputs (existingL1Count (pub w) (coins w))
   (run (publicSignal (pub w) (coins w)) (program (pub w) (coins w) n) (initial (pub w) (coins w)))
   (calls (publicSignal (pub w) (coins w)) (program (pub w) (coins w) n) (initial (pub w) (coins w)))) =
 (fun n => DIAG_inputs (existingL1Count (pub u) (coins u))
   (run (publicSignal (pub u) (coins u)) (program (pub u) (coins u) n) (initial (pub u) (coins u)))
   (calls (publicSignal (pub u) (coins u)) (program (pub u) (coins u) n) (initial (pub u) (coins u)))) :=
 DIAG_public_given_optionB pub coins (fun w => publicSignal (pub w) (coins w))
 (public_signal_satisfies_P pub coins publicSignal) program initial existingL1Count w u hp hc
#print axioms DIAG_optionB_public_signal
#print axioms V400_shared_signal
#print axioms public_signal_satisfies_P
#print axioms V400_component
#print axioms V400_write
#print axioms V400_flush
#print axioms V400_file
#print axioms V400_errno
#print axioms V400_strerror
#print axioms V400_environment
#print axioms V400_logger
#print axioms V400_backtrace
#print axioms V400_capture
#print axioms equal_failure_bit_not_equal_content
#print axioms failure_bit_agrees_for_distinct_errors
#print axioms shared_input_real_ideal
#print axioms advance_cursor
#print axioms store_cursor
#print axioms store_last_error
#print axioms advance_keeps_error
#print axioms write_success
#print axioms write_failure
#print axioms write_events_public
#print axioms write_terminal_public
#print axioms partial_delivery_keeps_requested
#print axioms failed_write_keeps_request
#print axioms write_errno_history
#print axioms status_success
#print axioms status_failure
#print axioms status_preserves_failure
#print axioms flush_failure
#print axioms file_failure
#print axioms errno_reply
#print axioms strerror_reply
#print axioms environment_reply
#print axioms logger_reply
#print axioms backtrace_configuration_reply
#print axioms capture_configuration_reply
#print axioms effect_public
#print axioms effect_has_value
#print axioms effect_advances_cursor
#print axioms lossy_public
#print axioms lossy_length_public
#print axioms returned_error_public
#print axioms interrupted_class_public
#print axioms fd1_public
#print axioms fd2_public
#print axioms answer_correct
#print axioms run_done
#print axioms run_returned
#print axioms run_call_is_bind
#print axioms run_public
#print axioms calls_public
#print axioms run_events_public
#print axioms run_terminal_public
#print axioms run_state_public
#print axioms run_has_value
#print axioms returned_order
#print axioms return_preserves_calls
#print axioms call_is_first
#print axioms write_success_continuation
#print axioms write_error_continuation
#print axioms interrupted_keeps_prior_delivery
#print axioms flush_failure_continuation
#print axioms file_failure_continuation
#print axioms strerror_is_precursor
#print axioms os_failure_does_not_erase_returned
#print axioms all_prefix_programs_public
#print axioms occurrence_order_content_joint
#print axioms native_write_ok
#print axioms native_write_error
#print axioms os_interrupted_guard
#print axioms interrupted_drop_no_custom_payload
#print axioms optionB_write_step_public
#print axioms optionB_write_prefix_public
#print axioms optionB_interrupted_retry
#print axioms optionB_noninterrupted_return
#print axioms optionB_every_write_prefix
#print axioms nonce_failure_retained
#print axioms nonce_success_resets_error
#print axioms nonce_last_error_kind
#print axioms nonce_wrapper_public
#print axioms DIAG_public_given_optionB
#print axioms DIAG_complete_decoder
#print axioms DIAG_retained_state
#print axioms DIAG_native_handoff
#print axioms DIAG_signal_not_fixed
#print axioms DIAG_witness_operand_obstruction
#print axioms print_to_message_public
#print axioms print_to_message_length_public
#print axioms optionB_bound_unchanged
#print DIAG_optionB_public_signal
#print DIAG_native_handoff
end PV_DIAG7
