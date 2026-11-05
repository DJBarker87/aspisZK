import NHY_EntryHeader
import NHY_RegistryHeader
import NHY_WindowTransport
import NHY_ParsedBodies
import NHY_FieldRead
import NHY_ExactArray
import NHY_SliceRead
import NHY_ZeroLoop
import NHY_ZeroStep
import NHY_ZeroRun
import NHY_AllZeroBridge
import NHY_NCXValidators
import NHJ_COMBINED_IMPORT
import NGK_COMBINED_IMPORT
import NHY_SnapshotRoot
import NHY_SnapshotJoin
import NHY_SnapshotHeader
import NHY_ErrorFragments
import NHY_AfterAuth
import NHY_RegistryPolicyCut
import NHY_StringAppend
import NHY_CandidateBoundary
import NHY_PolicyModel
import NHY_RegistryPipeline
import NHY_RegistryPrimitives
import NHY_RegistrySlots
import NHY_RegistryReference
import NHY_PolicyReference
import NHY_ZeroBinding
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms NHY_SnapshotRoot.returning
#print axioms NHY_SnapshotRoot.root_not_blocked
#print axioms NHY_SnapshotJoin.rejected
#print axioms NHY_SnapshotJoin.both_arms
#print axioms NHY_SnapshotJoin.source

#print axioms NHY_SnapshotHeader.chain
#print axioms NHY_SnapshotHeader.clone_domain
#print axioms NHY_SnapshotHeader.clone_reply

#print axioms NHY_ErrorFragments.ordered_message
#print axioms NHY_ErrorFragments.syscall_bytes
#print axioms NHY_ErrorFragments.table
#print axioms NHY_ErrorFragments.logger
#print axioms NHY_AfterAuth.success
#print axioms NHY_AfterAuth.rejected
#print axioms NHY_AfterAuth.child_error
#print axioms NHY_RegistryPolicyCut.policy_error
#print axioms NHY_StringAppend.prefix_frame
#print axioms NHY_StringAppend.appended_byte
#print axioms NHY_StringAppend.contents
#print axioms NHY_StringAppend.literal_frame
#print axioms AspisR1.NHL_Tx1Model.source
#print axioms NHT_Tx2AuthModel.source
#print axioms NHT_AdapterInstall.cohort_slot
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms NHY_PolicyModel.extracted
#print axioms NHY_PolicyModel.value
#print axioms NHY_PolicyModel.actual_slot
#print axioms NHY_RegistryPipeline.paused_v1
#print axioms NHY_RegistryPipeline.immutable_v1
#print axioms NHY_RegistryPipeline.paused_v2
#print axioms NHY_RegistryPipeline.immutable_v2
#print axioms NHY_RegistryPipeline.policy
#print axioms NHY_RegistryPipeline.status
#print axioms NHY_RegistryPrimitives.retirement_v1
#print axioms NHY_RegistryPrimitives.retirement_v2
#print axioms NHY_RegistryPrimitives.pending
#print axioms NHY_RegistryPrimitives.active
#print axioms NHY_RegistryPrimitives.paused
#print axioms NHY_RegistryPrimitives.retired
#print axioms NHY_RegistryPrimitives.invalid
#print axioms NHY_RegistrySlots.immutable_v1
#print axioms NHY_RegistrySlots.paused_v1
#print axioms NHY_RegistrySlots.immutable_v2
#print axioms NHY_RegistrySlots.paused_v2
#print axioms NHY_RegistrySlots.digest_preserved
#print axioms NHY_RegistrySlots.error_preserved
#print axioms NHY_RegistryReference.flag_ref
#print axioms NHY_RegistryReference.retirement_ref
#print axioms NHY_RegistryReference.status_ref
#print axioms NHY_PolicyReference.policy_ref

#print axioms NHY_ZeroBinding.source

#print axioms NHY_ZeroLoop.done
#print axioms NHY_ZeroLoop.cont
#print axioms NHY_ZeroLoop.advance
#print axioms NHY_ZeroStep.read
#print axioms NHY_ZeroStep.terminal
#print axioms NHY_ZeroStep.step
#print axioms NHY_ZeroRun.run
#print axioms NHY_ZeroRun.value
#print axioms NHY_AllZeroBridge.list_zero
#print axioms NHY_AllZeroBridge.view_zero
#print axioms NHY_AllZeroBridge.array_zero
#print axioms NHY_AllZeroBridge.source
#print axioms NHY_NCXValidators.registry_source
#print axioms NHY_NCXValidators.entry_source
#print axioms NHY_NCXValidators.result_roundtrip
#print axioms NHY_NCXValidators.inverse_result_roundtrip
#print axioms NHY_NCXValidators.zero_child

#print axioms NHY_SliceRead.length
#print axioms NHY_SliceRead.read
#print axioms NHY_ExactArray.cast
#print axioms NHY_FieldRead.range
#print axioms NHY_FieldRead.bytes32
#print axioms NHY_FieldRead.word64
#print axioms NHY_ParsedBodies.registry
#print axioms NHY_ParsedBodies.entry
#print axioms NHY_WindowTransport.bounds
#print axioms NHY_WindowTransport.nested
#print axioms NHY_WindowTransport.field
#print axioms NHY_WindowTransport.array_domain
#print axioms NHY_WindowTransport.word_domain

#print axioms NHY_NCXValidators.native_registry_domain
#print axioms NHY_NCXValidators.native_entry_domain
#print axioms NHY_RegistryHeader.wrong_length
#print axioms NHY_RegistryHeader.wrong_magic
#print axioms NHY_RegistryHeader.wrong_version
#print axioms NHY_RegistryHeader.wrong_mode
#print axioms NHY_RegistryHeader.reserved
#print axioms NHY_EntryHeader.wrong_length
#print axioms NHY_EntryHeader.wrong_magic
#print axioms NHY_EntryHeader.wrong_version
#print axioms NHY_EntryHeader.wrong_mode
#print axioms NHY_EntryHeader.reserved
