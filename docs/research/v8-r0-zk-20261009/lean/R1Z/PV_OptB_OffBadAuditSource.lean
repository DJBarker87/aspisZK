import R1Z.PV_OptB_OffBadJoin
import R1Z.PV_OptB_BodySync
import R1Z.PV_OptB_DeployedOffBad
import R1Z.PV_OptB_WorldFrames
import R1Z.PV_OptB_FirstFailureOffBad
import R1Z.PV_OptB_ProjectionBoundary
set_option autoImplicit false
#print axioms R1Z.PV_OptB_OffBadJoin.Steps
#print axioms R1Z.PV_OptB_OffBadJoin.related_off_bad
#print axioms R1Z.PV_OptB_OffBadJoin.observations_off_bad
#print axioms R1Z.PV_OptB_OffBadJoin.independent_off_bad
#print axioms R1Z.PV_OptB_OffBadJoin.decoder_off_bad
#print axioms R1Z.PV_OptB_BodySync.finish
#print axioms R1Z.PV_OptB_BodySync.finish_related
#print axioms R1Z.PV_OptB_BodySync.attempt_finish
#print axioms R1Z.PV_OptB_BodySync.attempt_entropy_error
#print axioms R1Z.PV_OptB_BodySync.attempt_entropy_fail
#print axioms R1Z.PV_OptB_BodySync.attempt_entropy_div
#print axioms R1Z.PV_OptB_BodySync.attempt_related_at_same_state
#print axioms R1Z.PV_OptB_BodySync.body_steps_off_bad
#print axioms R1Z.PV_OptB_BodySync.body_signal_off_bad
#print axioms R1Z.PV_OptB_DeployedOffBad.conditional_off_bad
#print axioms R1Z.PV_OptB_WorldFrames.tapes
#print axioms R1Z.PV_OptB_WorldFrames.cursors
#print axioms R1Z.PV_OptB_WorldFrames.file_frame
#print axioms R1Z.PV_OptB_WorldFrames.time_frame
#print axioms R1Z.PV_OptB_WorldFrames.worker_frame
#print axioms R1Z.PV_OptB_WorldFrames.file_cursor
#print axioms R1Z.PV_OptB_WorldFrames.time_cursor
#print axioms R1Z.PV_OptB_WorldFrames.worker_cursor
#print axioms R1Z.PV_OptB_WorldFrames.time_unique
#print axioms R1Z.PV_OptB_WorldFrames.worker_unique
#print axioms R1Z.PV_OptB_WorldFrames.world_ext
#print axioms R1Z.PV_OptB_WorldFrames.flush_tapes
#print axioms R1Z.PV_OptB_WorldFrames.flush_cursors
#print axioms R1Z.PV_OptB_FirstFailureOffBad.execute_pair
#print axioms R1Z.PV_OptB_FirstFailureOffBad.signal_pair
#print axioms R1Z.PV_OptB_FirstFailureOffBad.independent_off_bad_on_first_failures
#print axioms R1Z.PV_OptB_ProjectionBoundary.erased_state_equal
#print axioms R1Z.PV_OptB_ProjectionBoundary.full_state_differs
#print axioms R1Z.PV_OptB_ProjectionBoundary.observation_factor_sufficient
#print axioms R1Z.PV_OptB_ProjectionBoundary.mapR_compose
#print axioms R1Z.PV_OptB_ProjectionBoundary.projected_observation_sufficient
#print R1Z.PV_OptB_OffBadJoin.Steps
#print R1Z.PV_OptB_DeployedOffBad.conditional_off_bad
#print R1Z.PV_RunJoin_UnifiedRetry.BodySourceLaw
