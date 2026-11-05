import NHJ_RouteFrame
import NHJ_RoutePacket
import NHJ_RouteReference
import NIM_NHJ_SnapshotPacket
import NHJ_SdkDomains
import NHJ_EntryDomains
import NHJ_SnapshotEntry
import NHJ_ClockPacket
import NHJ_RegistryHeader
import NHJ_DeployedIds
import NHJ_GuardPacket
import NHJ_CopyPacket
import NHJ_SdkBorrowPacket
import NHJ_IdPacket
import NHJ_SdkValidity
import NHJ_SdkBracket
import NIM_NHJ_SnapshotAssociation
import NHJ_StdCopy
import NGK_COMBINED_IMPORT
import NIM_NHD_COMBINED_IMPORT
import NIM_NHJ_ReadonlyPacket
import NHJ_DataPacket
import NHJ_LengthPacket
import NHJ_CheckpointPacket
import NHJ_DistinctPacket
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms NHJ_ReadonlyPacket.metadata
#print axioms NHJ_ReadonlyPacket.readonly

#print axioms NHJ_DataPacket.exact_error
#print axioms NHJ_DataPacket.substitute
#print axioms NHJ_DataPacket.storage_domain

#print axioms NHJ_LengthPacket.substitute
#print axioms NHJ_LengthPacket.storage_domain
#print axioms NHJ_CheckpointPacket.decode_encode
#print axioms NHJ_CheckpointPacket.substitute

#print axioms NHJ_DistinctPacket.same_comparison
#print axioms NHJ_DistinctPacket.seven
#print axioms NHJ_DistinctPacket.three

#print axioms NHJ_StdCopy.map_bytes
#print axioms NHJ_StdCopy.list_clone
#print axioms NHJ_StdCopy.to_vec_exact
#print axioms NHJ_StdCopy.length_law
#print axioms NHJ_SnapshotAssociation.source
#print axioms NHJ_SdkBracket.filter_fresh
#print axioms NHJ_SdkBracket.shared_release
#print axioms NHJ_SdkBracket.shared_release_ambient
#print axioms NHJ_SdkValidity.tokens_fresh
#print axioms NHJ_SdkValidity.shared_count
#print axioms NHJ_SdkValidity.exclusive_count
#print axioms NHJ_SdkValidity.counter
#print axioms NHJ_SdkValidity.acquired_valid
#print axioms NHJ_SdkValidity.ambient_valid

#print axioms NHJ_IdPacket.extracted
#print axioms NHJ_IdPacket.pool_slot
#print axioms NHJ_IdPacket.registry_slot
#print axioms NHJ_IdPacket.digest_preserved
#print axioms NHJ_IdPacket.error_preserved
#print axioms NHJ_SdkBorrowPacket.returning_shared
#print axioms NHJ_SdkBorrowPacket.rejected_shared
#print axioms NHJ_CopyPacket.initialized
#print axioms NHJ_CopyPacket.contents
#print axioms NHJ_CopyPacket.source_contents
#print axioms NHJ_GuardPacket.decode_encode
#print axioms NHJ_GuardPacket.first_error
#print axioms NHJ_GuardPacket.complete

#print axioms NHJ_DeployedIds.pool_actual
#print axioms NHJ_DeployedIds.registry_actual

#print axioms NHJ_ClockPacket.success
#print axioms NHJ_ClockPacket.error_payload
#print axioms NHJ_ClockPacket.unused_fields
#print axioms NHJ_RegistryHeader.first_error

#print axioms NHJ_SnapshotEntry.len_iff
#print axioms NHJ_SnapshotEntry.source
#print axioms NHJ_EntryDomains.source_domain
#print axioms NHJ_EntryDomains.first_table
#print axioms NHJ_EntryDomains.second_table
#print axioms NHJ_EntryDomains.allocation_bounds
#print axioms NHJ_SdkDomains.member_bound
#print axioms NHJ_SdkDomains.not_found
#print axioms NHJ_SdkDomains.enabled_exists
#print axioms NHJ_SdkDomains.counter_cases
#print axioms NHJ_SnapshotPacket.cohort_return
#print axioms NHJ_SnapshotPacket.caller_domains
#print axioms NHJ_SnapshotPacket.bracket_all
#print axioms NHJ_RoutePacket.cohort
#print axioms NHJ_RoutePacket.extracted
#print axioms NHJ_RoutePacket.associate
#print axioms NHJ_RouteFrame.four_length
#print axioms NHJ_RouteFrame.four_window
#print axioms NHJ_RouteFrame.rejected_short
