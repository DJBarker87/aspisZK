import NIM_COMBINED_IMPORT
import NIM_NHJ_COMBINED_IMPORT
import NIS_ReturnedWrite
import NIS_NativeSdkRelease
import NIS_NativeSdkCopy
import NIS_SdkCopyFields
import NIS_SdkCopyCanonical
import NIS_ExclusiveRelease
import NIS_ExclusiveEntry
import NIS_SdkWriteLoop
import NIS_SdkWriteFrame
import NIS_ActiveSlots
import NIS_StringCleanup
import NIS_ErrorJoin
import NIS_ArgumentMetadata
import NIS_AuthGuardsV2
import NIS_AuthGuardsV1
import NIS_GuardPrefix
import NIM_NHY_COMBINED_IMPORT
import NGK_COMBINED_IMPORT
import NIS_FormatterPackets
import NIS_EntryStatus
import NIS_EntryRecord
import NIS_EntryModel
import NIS_EntryJoin
import NIS_CheckpointAdvance
import NIS_CheckpointZeroStep
import NIS_CheckpointZeroRun

#print axioms AspisR1.RPx_Deployed.deployed
#print axioms NIJ_FormatterPackets.string_log
#print axioms NIJ_FormatterPackets.decoded_bytes
#print axioms NIJ_FormatterPackets.abort_prefix
#print axioms NIJ_FormatterPackets.cleanup_frame
#print axioms NIJ_EntryStatus.source
#print axioms NIJ_EntryStatus.rejected
#print axioms NIJ_EntryRecord.domain
#print axioms NIJ_EntryRecord.status_error
#print axioms NIJ_EntryModel.source
#print axioms NIJ_EntryJoin.source
#print axioms NIJ_EntryJoin.cohort
#print axioms NIJ_EntryJoin.digest_error_frame
#print axioms NIJ_CheckpointAdvance.value
#print axioms NIJ_CheckpointZeroStep.terminal
#print axioms NIJ_CheckpointZeroStep.step
#print axioms NIJ_CheckpointZeroStep.suffix_byte
#print axioms NIJ_CheckpointZeroStep.next_value
#print axioms NIJ_CheckpointZeroRun.run
#print axioms NIJ_CheckpointZeroRun.value

#print axioms AspisR1.RPx_Deployed.deployed
#print axioms NIJ_GuardPrefix.trace
#print axioms NIJ_GuardPrefix.bound
#print axioms NIJ_GuardPrefix.result
#print axioms NIJ_GuardPrefix.first_error
#print axioms NIJ_AuthGuardsV1.registry_trace
#print axioms NIJ_AuthGuardsV1.entry_trace
#print axioms NIJ_AuthGuardsV1.registry_domain
#print axioms NIJ_AuthGuardsV1.entry_domain
#print axioms NIJ_AuthGuardsV2.registry_trace
#print axioms NIJ_AuthGuardsV2.entry_trace
#print axioms NIJ_AuthGuardsV2.registry_domain
#print axioms NIJ_AuthGuardsV2.entry_domain
#print axioms NIJ_ArgumentMetadata.capacity
#print axioms NIJ_ArgumentMetadata.as_str_none
#print axioms NIJ_ArgumentMetadata.choose
#print axioms NIJ_ArgumentMetadata.message_bound
#print axioms NIJ_ErrorJoin.bytes
#print axioms NIJ_ErrorJoin.source
#print axioms NIJ_ErrorJoin.exhaustive
#print axioms NIJ_ErrorJoin.abort_prefix
#print axioms NIJ_StringCleanup.outside
#print axioms NIJ_StringCleanup.inside
#print axioms NIJ_StringCleanup.account_frame
#print axioms NIJ_StringCleanup.growth_frame

#print axioms AspisR1.RPx_Deployed.deployed
#print axioms NIJ_ActiveSlots.op29_exact
#print axioms NIJ_ActiveSlots.op30_exact
#print axioms NIJ_ActiveSlots.selected
#print axioms NIJ_ActiveSlots.digest_error_frame
#print axioms NIJ_ActiveSlots.retirement_v1
#print axioms NIJ_ActiveSlots.retirement_v2
#print axioms NIJ_SdkWriteFrame.byte
#print axioms NIJ_SdkWriteFrame.other_byte
#print axioms NIJ_SdkWriteFrame.other_cell
#print axioms NIJ_SdkWriteFrame.descriptor
#print axioms NIJ_SdkWriteFrame.frame
#print axioms NIJ_SdkWriteFrame.valid
#print axioms NIJ_SdkWriteLoop.contents
#print axioms NIJ_SdkWriteLoop.outside
#print axioms NIJ_SdkWriteLoop.other_cell
#print axioms NIJ_SdkWriteLoop.descriptor
#print axioms NIJ_SdkWriteLoop.valid
#print axioms NIJ_ExclusiveEntry.valid
#print axioms NIJ_ExclusiveEntry.entry_valid
#print axioms NIJ_ExclusiveEntry.counter
#print axioms NIJ_ExclusiveEntry.found
#print axioms NIJ_ExclusiveRelease.acquired
#print axioms NIJ_ExclusiveRelease.write_commutes
#print axioms NIJ_ExclusiveRelease.copied
#print axioms NIJ_SdkCopyCanonical.unchanged
#print axioms NIJ_SdkCopyCanonical.payload
#print axioms NIJ_SdkCopyCanonical.source
#print axioms NIJ_SdkCopyFields.guards
#print axioms NIJ_SdkCopyFields.counter
#print axioms NIJ_SdkCopyFields.lookup
#print axioms NIJ_SdkCopyFields.ambient
#print axioms NIJ_NativeSdkCopy.source
#print axioms NIJ_NativeSdkCopy.canonical
#print axioms NIJ_NativeSdkRelease.source
#print axioms NIJ_ReturnedWrite.bytes
