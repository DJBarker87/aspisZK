import NDB_DigestDecision
import NDB_DigestReject
import NDB_FrontierReject
import NDB_FrontierRun
import NDB_MasterDecision
import NDB_PrimaryBytes
import NDB_PrimaryDigestRun
import NDB_PrimaryDigestStep
import NDB_PrimaryDigestTransport
import NDB_PrimaryEquality
import NDB_PrimaryFrontierRun
import NDB_PrimaryFrontierStep
import NDB_PrimarySequence
import NDB_PrimaryWindow
import NDB_PrimaryWords
import NDB_RecordExt
import NDB_RejectInduction
import NDB_RejectWitness
import NDB_ScanDecision
import NDB_SequenceDecision
import NDB_WindowGeometry
import NCV_InstallationSupport
#print axioms NDB_DigestDecision.loop_value
#print axioms NDB_DigestDecision.value
#print axioms NDB_DigestReject.rejected
#print axioms NDB_DigestReject.step
#print axioms NDB_FrontierReject.digest_error
#print axioms NDB_FrontierReject.rejected
#print axioms NDB_FrontierReject.vacant_error
#print axioms NDB_FrontierRun.value
#print axioms NDB_MasterDecision.value
#print axioms NDB_PrimaryBytes.value
#print axioms NDB_PrimaryDigestRun.value
#print axioms NDB_PrimaryDigestStep.step
#print axioms NDB_PrimaryDigestStep.terminal
#print axioms NDB_PrimaryDigestTransport.chunk
#print axioms NDB_PrimaryDigestTransport.source
#print axioms NDB_PrimaryDigestTransport.subwindow
#print axioms NDB_PrimaryDigestTransport.value
#print axioms NDB_PrimaryEquality.digest_equal
#print axioms NDB_PrimaryEquality.digest_reflexive
#print axioms NDB_PrimaryFrontierRun.value
#print axioms NDB_PrimaryFrontierStep.step
#print axioms NDB_PrimaryFrontierStep.terminal
#print axioms NDB_PrimarySequence.step
#print axioms NDB_PrimarySequence.terminal
#print axioms NDB_PrimarySequence.value
#print axioms NDB_PrimaryWindow.bytes
#print axioms NDB_PrimaryWindow.bytes32
#print axioms NDB_PrimaryWindow.coordinate
#print axioms NDB_PrimaryWindow.word32
#print axioms NDB_PrimaryWindow.word64
#print axioms NDB_PrimaryWords.add_read
#print axioms NDB_PrimaryWords.word32
#print axioms NDB_PrimaryWords.word64
#print axioms NDB_RecordExt.array
#print axioms NDB_RecordExt.checkpoint
#print axioms NDB_RecordExt.identity
#print axioms NDB_RecordExt.master
#print axioms NDB_RecordExt.policy
#print axioms NDB_RejectInduction.run
#print axioms NDB_RejectWitness.run
#print axioms NDB_ScanDecision.run
#print axioms NDB_SequenceDecision.valid
#print axioms NDB_SequenceDecision.valid_loop
#print axioms NDB_SequenceDecision.zero
#print axioms NDB_SequenceDecision.zero_loop
#print axioms NDB_WindowGeometry.checkpoint
#print axioms NDB_WindowGeometry.lane
#print axioms NDB_WindowGeometry.master
#print axioms NDB_WindowGeometry.row
#print axioms NCV_Install.op48
#print axioms NCV_Install.op49
#print axioms NCV_Install.op50
#print axioms NCV_InstallationSupport.sdk_master
#print axioms NCV_InstallationSupport.sdk_checkpoint
#print axioms NCV_InstallationSupport.sdk_lane
