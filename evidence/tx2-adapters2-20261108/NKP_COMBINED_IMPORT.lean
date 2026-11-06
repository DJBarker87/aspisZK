import NKH_COMBINED_IMPORT
import NKF_COMBINED_IMPORT
import NKP_BoxCuts
import NKP_BoxUniformity
import NKP_LaneCuts
import NKP_LaneInduction
import NKP_LaneCarrier
import NKP_LaneCompletion
import NKP_RegistryCuts

#check AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.RPx_Deployed.deployed
#check NKF_BoxModel.box_value
#print axioms NKF_BoxModel.box_value
#check NKF_BoxModel.error
#print axioms NKF_BoxModel.error
#check NKF_BoxModel.success
#print axioms NKF_BoxModel.success
#check NKF_BoxModel.abort
#print axioms NKF_BoxModel.abort
#check NKF_BoxModel.diverge
#print axioms NKF_BoxModel.diverge
#check NKF_BoxModel.congruence
#print axioms NKF_BoxModel.congruence
#check NKF_MasterBox.raw_child
#print axioms NKF_MasterBox.raw_child
#check NKF_MasterBox.source
#print axioms NKF_MasterBox.source
#check NKF_CheckpointBox.raw_child
#print axioms NKF_CheckpointBox.raw_child
#check NKF_CheckpointBox.source
#print axioms NKF_CheckpointBox.source
#check NKF_BoxInstall.actual_slots
#print axioms NKF_BoxInstall.actual_slots
#check NKF_BoxInstall.digest_error_frame
#print axioms NKF_BoxInstall.digest_error_frame
#check NKF_ArrayFrame.array_ext
#print axioms NKF_ArrayFrame.array_ext
#check NKF_ArrayFrame.point_frame
#print axioms NKF_ArrayFrame.point_frame
#check NKF_BoxFields.master
#print axioms NKF_BoxFields.master
#check NKF_BoxFields.checkpoint
#print axioms NKF_BoxFields.checkpoint
#check NKF_Windows.bounded_cells
#print axioms NKF_Windows.bounded_cells
#check NKF_Windows.word_cells
#print axioms NKF_Windows.word_cells
#check NKF_Windows.master_fields
#print axioms NKF_Windows.master_fields
#check NKF_Windows.checkpoint_fields
#print axioms NKF_Windows.checkpoint_fields
#check NKF_Roots.master_tail
#print axioms NKF_Roots.master_tail
#check NKF_Roots.checkpoint_tail
#print axioms NKF_Roots.checkpoint_tail
#check NKF_Roots.master
#print axioms NKF_Roots.master
#check NKF_Roots.checkpoint
#print axioms NKF_Roots.checkpoint
#check NKF_LaneTrace.iteration_frame
#print axioms NKF_LaneTrace.iteration_frame
#check NKF_LaneTrace.error_no_write
#print axioms NKF_LaneTrace.error_no_write
#check NKF_LaneTrace.rejected_write
#print axioms NKF_LaneTrace.rejected_write
#check NKF_LaneTrace.loop_frame
#print axioms NKF_LaneTrace.loop_frame
#check NKF_LaneTrace.abort_no_suffix
#print axioms NKF_LaneTrace.abort_no_suffix
#check NKF_PdaModel.success
#print axioms NKF_PdaModel.success
#check NKF_PdaModel.error
#print axioms NKF_PdaModel.error
#check NKF_PdaModel.abort
#print axioms NKF_PdaModel.abort
#check NKF_PdaModel.divergence
#print axioms NKF_PdaModel.divergence
#check NKF_PdaModel.no_suffix
#print axioms NKF_PdaModel.no_suffix
#check NKF_SeedWindows.bytes
#print axioms NKF_SeedWindows.bytes
#check NKF_SeedWindows.seeds
#print axioms NKF_SeedWindows.seeds
#check NKF_SeedWindows.invocation
#print axioms NKF_SeedWindows.invocation
#check NKF_LaneFactor.success_step
#print axioms NKF_LaneFactor.success_step
#check NKF_LaneFactor.selected
#print axioms NKF_LaneFactor.selected
#check NKF_LaneFactor.coordinate
#print axioms NKF_LaneFactor.coordinate
#check NKF_LaneFactor.node_eq
#print axioms NKF_LaneFactor.node_eq
#check NKF_LaneFactor.accepted_guard
#print axioms NKF_LaneFactor.accepted_guard
#check NKF_LaneFactor.window_bounds
#print axioms NKF_LaneFactor.window_bounds
#check NKF_LaneFactor.distinct_windows
#print axioms NKF_LaneFactor.distinct_windows
#check NKF_LaneConstructor.tree
#print axioms NKF_LaneConstructor.tree
#check NKF_LaneConstructor.constructor
#print axioms NKF_LaneConstructor.constructor
#check NKF_LanePrefix.log_prefix
#print axioms NKF_LanePrefix.log_prefix
#check NKF_LanePrefix.log_bound
#print axioms NKF_LanePrefix.log_bound
#check NKF_LanePrefix.success_log
#print axioms NKF_LanePrefix.success_log
#check NKP_BoxCuts.master_tail
#print axioms NKP_BoxCuts.master_tail
#check NKP_BoxCuts.checkpoint_tail
#print axioms NKP_BoxCuts.checkpoint_tail
#check NKP_BoxCuts.master
#print axioms NKP_BoxCuts.master
#check NKP_BoxCuts.checkpoint
#print axioms NKP_BoxCuts.checkpoint
#check NKP_BoxUniformity.master_bytes_irrelevant
#print axioms NKP_BoxUniformity.master_bytes_irrelevant
#check NKP_BoxUniformity.checkpoint_bytes_irrelevant
#print axioms NKP_BoxUniformity.checkpoint_bytes_irrelevant
#check NKP_BoxUniformity.master_any_bytes
#print axioms NKP_BoxUniformity.master_any_bytes
#check NKP_BoxUniformity.checkpoint_any_bytes
#print axioms NKP_BoxUniformity.checkpoint_any_bytes
#check NKP_LaneCuts.iteration
#print axioms NKP_LaneCuts.iteration
#check NKP_LaneCuts.constructor
#print axioms NKP_LaneCuts.constructor
#check NKP_LaneCuts.absolute_window
#print axioms NKP_LaneCuts.absolute_window
#check NKP_LaneInduction.compose
#print axioms NKP_LaneInduction.compose
#check NKP_LaneInduction.chronological
#print axioms NKP_LaneInduction.chronological
#check NKP_LaneCarrier.node_at
#print axioms NKP_LaneCarrier.node_at
#check NKP_LaneCarrier.frontier_at
#print axioms NKP_LaneCarrier.frontier_at
#check NKP_LaneCarrier.root_at
#print axioms NKP_LaneCarrier.root_at
#check NKP_LaneCarrier.frontier_row
#print axioms NKP_LaneCarrier.frontier_row
#check NKP_LaneCarrier.returned
#print axioms NKP_LaneCarrier.returned
#check NKP_LaneCompletion.loop_error
#print axioms NKP_LaneCompletion.loop_error
#check NKP_LaneCompletion.rejected_root
#print axioms NKP_LaneCompletion.rejected_root
#check NKP_LaneCompletion.constructed
#print axioms NKP_LaneCompletion.constructed
#check NKP_LaneCompletion.log_frame
#print axioms NKP_LaneCompletion.log_frame
#check NKP_LaneCompletion.compose
#print axioms NKP_LaneCompletion.compose
#check NKP_RegistryCuts.comparison
#print axioms NKP_RegistryCuts.comparison
#check NKP_RegistryCuts.rejection_no_suffix
#print axioms NKP_RegistryCuts.rejection_no_suffix
#check NKP_RegistryCuts.accepted_continuation
#print axioms NKP_RegistryCuts.accepted_continuation

set_option pp.proofs false in
#print NKP_BoxCuts.MasterCut

set_option pp.proofs false in
#print NKP_BoxCuts.CheckpointCut

set_option pp.proofs false in
#print NKP_BoxCuts.MasterReturned

set_option pp.proofs false in
#print NKP_BoxCuts.CheckpointReturned

set_option pp.proofs false in
#print NKP_LaneCuts.IterationCut

set_option pp.proofs false in
#print NKP_BoxCuts.master

set_option pp.proofs false in
#print NKP_BoxCuts.checkpoint
