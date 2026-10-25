import SdkC_Accounting
import SdkC_Authentication
import SdkC_BatchPair
import SdkC_BatchSource
import SdkC_FirstAuthentication
import SdkC_GlobalRecovery
import SdkC_NativeNode
import SdkC_Nonvacuity
import SdkC_Oracle
import SdkC_Progress
import SdkC_Replay
import SdkC_Source
import SdkC_SourceLaws
import Op5T_Final
set_option autoImplicit false
#print axioms AspisR1.SdkC_Accounting.attempts
#print axioms AspisR1.SdkC_Accounting.first_reads
#print axioms AspisR1.SdkC_Accounting.ideal_reads
#print axioms AspisR1.SdkC_Accounting.collision_bound
#print axioms AspisR1.SdkC_Accounting.leaf_range_budget
#print axioms AspisR1.SdkC_Accounting.leaf_budget
#print axioms AspisR1.SdkC_Authentication.ideal_value
#print axioms AspisR1.SdkC_Authentication.stage_acceptance
#print axioms AspisR1.SdkC_Authentication.stage_paths
#print axioms AspisR1.SdkC_BatchPair.returning
#print axioms AspisR1.SdkC_BatchPair.same_pair
#print axioms AspisR1.SdkC_BatchPair.accepted_pair
#print axioms AspisR1.SdkC_BatchSource.erasure
#print axioms AspisR1.SdkC_BatchSource.map_erasure
#print axioms AspisR1.SdkC_BatchSource.current_source
#print axioms AspisR1.SdkC_BatchSource.stage_source
#print axioms AspisR1.SdkC_FirstAuthentication.current_acceptance
#print axioms AspisR1.SdkC_FirstAuthentication.current_paths
#print axioms AspisR1.SdkC_GlobalRecovery.indexed_recovery_or_collision
#print axioms AspisR1.SdkC_GlobalRecovery.collision_bound
#print axioms AspisR1.SdkC_NativeNode.erase_writer
#print axioms AspisR1.SdkC_NativeNode.erase_checked
#print axioms AspisR1.SdkC_NativeNode.erase_conditional
#print axioms AspisR1.SdkC_NativeNode.erase_node
#print axioms AspisR1.SdkC_NativeNode.source_node
#print axioms AspisR1.SdkC_NativeNode.source_leaf
#print axioms AspisR1.SdkC_Nonvacuity.model_syscall
#print axioms AspisR1.SdkC_Nonvacuity.installed_leaf
#print axioms AspisR1.SdkC_Nonvacuity.fixture
#print axioms AspisR1.SdkC_Oracle.readLog_append
#print axioms AspisR1.SdkC_Oracle.accepted_transport
#print axioms AspisR1.SdkC_Oracle.accepted_exact
#print axioms AspisR1.SdkC_Progress.program_reify
#print axioms AspisR1.SdkC_Progress.node_transport
#print axioms AspisR1.SdkC_Progress.node_progress
#print axioms AspisR1.SdkC_Progress.rows_eq_source
#print axioms AspisR1.SdkC_Replay.replay_bound
#print axioms AspisR1.SdkC_Replay.firstReads_append_le
#print axioms AspisR1.SdkC_Replay.augmented_bound
#print axioms AspisR1.SdkC_Replay.collision_bound
#print axioms AspisR1.SdkC_Replay.cut_append
#print axioms AspisR1.SdkC_Replay.recover_or_collision
#print axioms AspisR1.SdkC_Source.erasure
#print axioms AspisR1.SdkC_Source.prefix_preserved
#print axioms AspisR1.SdkC_Source.associated
#print axioms AspisR1.SdkC_Source.consistent
#print axioms AspisR1.SdkC_Source.digest_erasure
#print axioms AspisR1.SdkC_Source.digest_trace
#print axioms AspisR1.SdkC_Source.installed_digest
#print axioms AspisR1.SdkC_Source.erasure_to
#print axioms AspisR1.SdkC_Source.run_bind
#print axioms AspisR1.SdkC_Source.read_count
#print axioms AspisR1.SdkC_Source.no_fabricated_reply
#print axioms AspisR1.SdkC_Source.returning_digest
#print axioms AspisR1.SdkC_Source.failed_digest
