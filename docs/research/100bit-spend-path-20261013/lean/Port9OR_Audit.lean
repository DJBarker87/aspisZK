import Port9OR_Batch
import Port9OR_BatchCut
import Port9OR_BatchLaw
import Port9OR_BatchLoop
import Port9OR_BatchProgress
import Port9OR_BatchStep
import Port9OR_BatchTree
import Port9OR_Bodies
import Port9OR_Bridge
import Port9OR_Budget
import Port9OR_Checksum
import Port9OR_Code
import Port9OR_Driver
import Port9OR_FirstBatch
import Port9OR_Installed
import Port9OR_Law
import Port9OR_P6Levels
import Port9OR_P6Node
import Port9OR_P6Progress
import Port9OR_P6Rows
import Port9OR_P6Verify
import Port9OR_Reached
import Port9OR_Rejection
import Port9OR_Reply

set_option autoImplicit false
#print AspisR1.CheckpointBytes5Inputs.Oracle
#print AspisR1.Port9OR_Code.native
#print AspisR1.Port9OR_Code.program
#print AspisR1.Port9OR_Bodies.native
#print AspisR1.Port9OR_Installed.implementation
#check @AspisR1.Port9OR_Code.correspondence
#check @AspisR1.Port9OR_Bodies.reader_value
#check @AspisR1.Port9OR_Bodies.reader_effects
#check @AspisR1.Port9OR_Law.reader_lazy
#check @AspisR1.Port9OR_Checksum.checksum_branches
#check @AspisR1.Port9OR_Bridge.reader_inverse
#check @AspisR1.Port9OR_Budget.reader_count
#check @AspisR1.Port9OR_P6Verify.source
#check @AspisR1.Port9OR_Batch.source
#check @AspisR1.Port9OR_Installed.effects
#check @AspisR1.Port9OR_FirstBatch.first_batch
#check @AspisR1.Port9OR_BatchLaw.batch_lazy
#check @AspisR1.Port9OR_Rejection.no_sampler

#print axioms AspisR1.Port9OR_Batch.values_source
#print axioms AspisR1.Port9OR_Batch.source
#print axioms AspisR1.Port9OR_BatchCut.source
#print axioms AspisR1.Port9OR_BatchLaw.batch_lazy
#print axioms AspisR1.Port9OR_BatchLoop.body_dictionary
#print axioms AspisR1.Port9OR_BatchLoop.source
#print axioms AspisR1.Port9OR_BatchProgress.advance
#print axioms AspisR1.Port9OR_BatchStep.pair_match
#print axioms AspisR1.Port9OR_BatchStep.verify_source
#print axioms AspisR1.Port9OR_BatchStep.source
#print axioms AspisR1.Port9OR_BatchTree.source_factor
#print axioms AspisR1.Port9OR_BatchTree.source
#print axioms AspisR1.Port9OR_Bodies.native_stage
#print axioms AspisR1.Port9OR_Bodies.reader_value
#print axioms AspisR1.Port9OR_Bodies.writer_value
#print axioms AspisR1.Port9OR_Bodies.reader_effects
#print axioms AspisR1.Port9OR_Bodies.writer_effects
#print axioms AspisR1.Port9OR_Bodies.installed_reader
#print axioms AspisR1.Port9OR_Bodies.installed_writer
#print axioms AspisR1.Port9OR_Bridge.historical_at_native
#print axioms AspisR1.Port9OR_Bridge.reader_at_native
#print axioms AspisR1.Port9OR_Bridge.reader_success
#print axioms AspisR1.Port9OR_Bridge.reader_inverse
#print axioms AspisR1.Port9OR_Budget.count
#print axioms AspisR1.Port9OR_Budget.reader_bounded
#print axioms AspisR1.Port9OR_Budget.reader_count
#print axioms AspisR1.Port9OR_Checksum.list_compare
#print axioms AspisR1.Port9OR_Checksum.compare
#print axioms AspisR1.Port9OR_Checksum.checksum_branches
#print axioms AspisR1.Port9OR_Checksum.checksum_reject
#print axioms AspisR1.Port9OR_Checksum.discarded_reply
#print axioms AspisR1.Port9OR_Code.trace_value
#print axioms AspisR1.Port9OR_Code.correspondence
#print axioms AspisR1.Port9OR_Code.value
#print axioms AspisR1.Port9OR_Code.oracle
#print axioms AspisR1.Port9OR_Driver.head
#print axioms AspisR1.Port9OR_Driver.common_shape
#print axioms AspisR1.Port9OR_Driver.common_reader
#print axioms AspisR1.Port9OR_Driver.authenticated_common
#print axioms AspisR1.Port9OR_Driver.powers_reached
#print axioms AspisR1.Port9OR_Driver.first_reader
#print axioms AspisR1.Port9OR_FirstBatch.powers_logs
#print axioms AspisR1.Port9OR_FirstBatch.first_batch
#print axioms AspisR1.Port9OR_Installed.value
#print axioms AspisR1.Port9OR_Installed.effects
#print axioms AspisR1.Port9OR_Installed.installed
#print axioms AspisR1.Port9OR_Law.source_primitive
#print axioms AspisR1.Port9OR_Law.reader_lazy
#print axioms AspisR1.Port9OR_P6Levels.level_source
#print axioms AspisR1.Port9OR_P6Levels.level_preserve
#print axioms AspisR1.Port9OR_P6Levels.source
#print axioms AspisR1.Port9OR_P6Levels.eighteen
#print axioms AspisR1.Port9OR_P6Node.parent_source
#print axioms AspisR1.Port9OR_P6Node.node_source
#print axioms AspisR1.Port9OR_P6Node.node_value
#print axioms AspisR1.Port9OR_P6Progress.totality
#print axioms AspisR1.Port9OR_P6Progress.success
#print axioms AspisR1.Port9OR_P6Progress.node_progress
#print axioms AspisR1.Port9OR_P6Rows.source
#print axioms AspisR1.Port9OR_P6Rows.preserve
#print axioms AspisR1.Port9OR_P6Verify.source_factor
#print axioms AspisR1.Port9OR_P6Verify.source
#print axioms AspisR1.Port9OR_Reached.rejected
#print axioms AspisR1.Port9OR_Reached.pure_head
#print axioms AspisR1.Port9OR_Reached.after_powers
#print axioms AspisR1.Port9OR_Rejection.early
#print axioms AspisR1.Port9OR_Rejection.no_sampler
#print axioms AspisR1.Port9OR_Reply.state_digest
#print axioms AspisR1.Port9OR_Reply.digest_state
