import PV_DIAG5_Endpoint
/-! Exact existing RunJoin Result-only boundary. No decoder is defined or
installed. These necessities do not prove native prefix recovery, V038 or
its marginals. PV_RJ4IDB remains the owner of the observation decoder. -/
set_option autoImplicit false
noncomputable section
namespace PV_DIAG5
open R1Z.GamesR1 R1Z R0Z R0Z.JointView R0Z.FsStatement R1Z.Batched
local notation "K" => PrivacyR1AcctBasis.K
variable [ProverRwFull.ExternalTypes]
variable {CommitHandle Aux Coins N L C : Type}
variable (runtime : PV_RunJoin_Deployed.Runtime CommitHandle Aux Coins N L C)
theorem deployed_decoded_pair_same_result
 (h : HonestProver K) (x : Statement K CommitHandle) (w v : h.Instance)
 (r s : PV_RunJoin_Deployed.World runtime) (adv : R1Adv K CommitHandle Aux)
 (same : PV_RunJoin_Deployed.execute runtime h x w r = PV_RunJoin_Deployed.execute runtime h x v s) :
 (runtime.disclosed adv x (PV_RunJoin_Deployed.execute runtime h x w r),
  runtime.observerOracle adv x (PV_RunJoin_Deployed.execute runtime h x w r)) =
 (runtime.disclosed adv x (PV_RunJoin_Deployed.execute runtime h x v s),
  runtime.observerOracle adv x (PV_RunJoin_Deployed.execute runtime h x v s)) := by rw [same]
#print axioms deployed_decoded_pair_same_result
theorem deployed_complete_decision_same_result
 (h : HonestProver K) (x : Statement K CommitHandle) (w v : h.Instance)
 (r s : PV_RunJoin_Deployed.World runtime) (adv : R1Adv K CommitHandle Aux)
 (same : PV_RunJoin_Deployed.execute runtime h x w r = PV_RunJoin_Deployed.execute runtime h x v s) :
 adv.decide ⟨runtime.disclosed adv x (PV_RunJoin_Deployed.execute runtime h x w r),
  runtime.observerOracle adv x (PV_RunJoin_Deployed.execute runtime h x w r)⟩ =
 adv.decide ⟨runtime.disclosed adv x (PV_RunJoin_Deployed.execute runtime h x v s),
  runtime.observerOracle adv x (PV_RunJoin_Deployed.execute runtime h x v s)⟩ := by rw [same]
#print axioms deployed_complete_decision_same_result
end PV_DIAG5

#print axioms PV_DIAG5.callback_normal
#print axioms PV_DIAG5.clone_panic_no_push
#print axioms PV_DIAG5.clone_abort_no_push
#print axioms PV_DIAG5.clone_diverge_no_push
#print axioms PV_DIAG5.push_panic_no_address
#print axioms PV_DIAG5.push_abort_no_address
#print axioms PV_DIAG5.push_diverge_no_address
#print axioms PV_DIAG5.address_panic_keeps_push
#print axioms PV_DIAG5.address_abort_keeps_push
#print axioms PV_DIAG5.address_diverge_keeps_push
#print axioms PV_DIAG5.deployed_result_collision_requires_prefix
#print axioms PV_DIAG5.deployed_decoded_pair_same_result
#print axioms PV_DIAG5.deployed_complete_decision_same_result
#print axioms PV_DIAG5.honest_client_pieces
#print axioms PV_DIAG5.joint_capture_callback_bound
#print axioms PV_DIAG5.joint_frame_emission
#print axioms PV_DIAG5.coupled_scope_normal_cleanup
#print axioms PV_DIAG5.joint_delivered_request_and_frames
#print axioms PV_DIAG5.common_prefix_does_not_erase_suffix
#print axioms PV_DIAG5.ordered_events_preserve_occurrence
#print axioms PV_DIAG5.ordered_events_preserve_count
#print axioms PV_DIAG5.emit_empty
#print axioms PV_DIAG5.emit_cons
#print axioms PV_DIAG5.try_success
#print axioms PV_DIAG5.try_error_no_suffix
#print axioms PV_DIAG5.try_panic_no_suffix
#print axioms PV_DIAG5.try_abort_no_suffix
#print axioms PV_DIAG5.try_diverge_no_suffix
#print axioms PV_DIAG5.frame_no_symbols_raw
#print axioms PV_DIAG5.frame_symbols_order
#print axioms PV_DIAG5.try_coupled
#print axioms PV_DIAG5.emit_coupled
#print axioms PV_DIAG5.frame_coupled
#print axioms PV_DIAG5.disabled_no_capture
#print axioms PV_DIAG5.capture_false
#print axioms PV_DIAG5.capture_true
#print axioms PV_DIAG5.force_keeps_address
#print axioms PV_DIAG5.capture_enabled_panic
#print axioms PV_DIAG5.capture_enabled_abort
#print axioms PV_DIAG5.capture_enabled_diverge
#print axioms PV_DIAG5.unsupported_literal
#print axioms PV_DIAG5.disabled_literal
#print axioms PV_DIAG5.captured_full
#print axioms PV_DIAG5.captured_short
#print axioms PV_DIAG5.captured_invalid_short
#print axioms PV_DIAG5.output_from_joint_count_execution
#print axioms PV_DIAG5.output_retains_prefix
#print axioms PV_DIAG5.prefix_keeps_terminal
#print axioms PV_DIAG5.pieces_determine_events
#print axioms PV_DIAG5.pieces_determine_frames
#print axioms PV_DIAG5.pieces_determine_delivery
#print axioms PV_DIAG5.external_decoder_transport
#print axioms PV_DIAG5.result_only_recovery_obligation
#print axioms PV_DIAG5.cwd_before_body
#print axioms PV_DIAG5.cwd_abort_no_body
#print axioms PV_DIAG5.cwd_diverge_no_body
#print axioms PV_DIAG5.selected_return_drops_cwd
#print axioms PV_DIAG5.selected_panic_unwinds_cwd
#print axioms PV_DIAG5.selected_abort_no_cwd_drop
#print axioms PV_DIAG5.selected_diverge_no_cwd_drop
#print axioms PV_DIAG5.formatter_error_still_drops_cwd
#print axioms PV_DIAG5.empty_start_valid
#print axioms PV_DIAG5.push_start_valid
#print axioms PV_DIAG5.collect_start_valid
#print axioms PV_DIAG5.captured_start_valid
#print axioms PV_DIAG5.collect_frames
#print axioms PV_DIAG5.captured_frames_exact
#print axioms PV_DIAG5.start_getD_bound
#print axioms PV_DIAG5.actual_display_slice_valid
#print axioms PV_DIAG5.full_display_all
#print axioms PV_DIAG5.short_display_suffix
#print axioms PV_DIAG5.absent_start_all
#print axioms PV_DIAG5.at_end_no_frames
