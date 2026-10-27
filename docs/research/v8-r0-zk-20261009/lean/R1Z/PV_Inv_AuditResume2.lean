import R1Z.PV_Inv_DecodedSafety
import R1Z.PV_Inv_EmbedArithmetic
import R1Z.PV_Inv_EntriesSafety
import R1Z.PV_Inv_EntryReference
import R1Z.PV_Inv_EntrySafety
import R1Z.PV_Inv_GuardAllSites
import R1Z.PV_Inv_GuardRejectBoundary
import R1Z.PV_Inv_GuardSites
import R1Z.PV_Inv_GuardedNativeTests
import R1Z.PV_Inv_GuardedRegistry
import R1Z.PV_Inv_HeadlineCharge
import R1Z.PV_Inv_HeadlinePole
import R1Z.PV_Inv_InverseList
import R1Z.PV_Inv_MapGlobalRun
import R1Z.PV_Inv_MapGlobalStep
import R1Z.PV_Inv_MapReached
import R1Z.PV_Inv_MapSlots
import R1Z.PV_Inv_MaskBit
import R1Z.PV_Inv_MaskChunk0
import R1Z.PV_Inv_MaskChunk1
import R1Z.PV_Inv_MaskChunk2
import R1Z.PV_Inv_MaskPartition
import R1Z.PV_Inv_MaskSource
import R1Z.PV_Inv_NativeTupleJoin
import R1Z.PV_Inv_PackedInverseList
import R1Z.PV_Inv_PackedNormSafety
import R1Z.PV_Inv_PreGuard
import R1Z.PV_Inv_RawBankList
import R1Z.PV_Inv_RawBankRead
import R1Z.PV_Inv_RawBankTuple
import R1Z.PV_Inv_RegistryFamilyEight
import R1Z.PV_Inv_RegistryFamilyEvent
import R1Z.PV_Inv_RegistryFamilyMass
import R1Z.PV_Inv_RegistryInput
import R1Z.PV_Inv_RegistryPacking
import R1Z.PV_Inv_RegistryZeroEvent
import R1Z.PV_Inv_SourceConsumerJoin
import R1Z.PV_Inv_SourceProducerJoin
import R1Z.PV_Inv_TagWord
import R1Z.PV_Inv_TaggedBank
import R1Z.PV_Inv_TripleNorm
set_option autoImplicit false
#print axioms R1Z.PV_Inv_DecodedSafety.reached_nonzero
#print axioms R1Z.PV_Inv_EmbedArithmetic.add_value
#print axioms R1Z.PV_Inv_EmbedArithmetic.zero_value
#print axioms R1Z.PV_Inv_EmbedArithmetic.add_source
#print axioms R1Z.PV_Inv_EntriesSafety.all_entries
#print axioms R1Z.PV_Inv_EntryReference.member
#print axioms R1Z.PV_Inv_EntrySafety.producer
#print axioms R1Z.PV_Inv_EntrySafety.consumer
#print axioms R1Z.PV_Inv_GuardAllSites.active_mem
#print axioms R1Z.PV_Inv_GuardAllSites.sites_clear
#print axioms R1Z.PV_Inv_GuardRejectBoundary.rejects_iff
#print axioms R1Z.PV_Inv_GuardRejectBoundary.guarded_reject
#print axioms R1Z.PV_Inv_GuardSites.mem_producer
#print axioms R1Z.PV_Inv_GuardSites.mem_consumer
#print axioms R1Z.PV_Inv_GuardSites.row_clear
#print axioms R1Z.PV_Inv_GuardedNativeTests.tests_false
#print axioms R1Z.PV_Inv_GuardedRegistry.no_zero
#print axioms R1Z.PV_Inv_HeadlineCharge.mass_at_existing_term
#print axioms R1Z.PV_Inv_HeadlineCharge.numerical_term
#print axioms R1Z.PV_Inv_HeadlinePole.attempt_contained
#print axioms R1Z.PV_Inv_InverseList.all_success
#print axioms R1Z.PV_Inv_MapGlobalRun.run_map
#print axioms R1Z.PV_Inv_MapGlobalRun.empty_map
#print axioms R1Z.PV_Inv_MapGlobalStep.update_map
#print axioms R1Z.PV_Inv_MapGlobalStep.step_map
#print axioms R1Z.PV_Inv_MapReached.reached_map
#print axioms R1Z.PV_Inv_MapSlots.put_map
#print axioms R1Z.PV_Inv_MapSlots.step_map
#print axioms R1Z.PV_Inv_MaskBit.source_shift
#print axioms R1Z.PV_Inv_MaskBit.insert_bit
#print axioms R1Z.PV_Inv_MaskChunk0.block_0
#print axioms R1Z.PV_Inv_MaskChunk0.block_1
#print axioms R1Z.PV_Inv_MaskChunk0.block_2
#print axioms R1Z.PV_Inv_MaskChunk0.block_3
#print axioms R1Z.PV_Inv_MaskChunk0.block_4
#print axioms R1Z.PV_Inv_MaskChunk0.block_5
#print axioms R1Z.PV_Inv_MaskChunk0.block_6
#print axioms R1Z.PV_Inv_MaskChunk0.block_7
#print axioms R1Z.PV_Inv_MaskChunk0.block_8
#print axioms R1Z.PV_Inv_MaskChunk0.block_9
#print axioms R1Z.PV_Inv_MaskChunk0.block_10
#print axioms R1Z.PV_Inv_MaskChunk0.block_11
#print axioms R1Z.PV_Inv_MaskChunk0.block_12
#print axioms R1Z.PV_Inv_MaskChunk0.block_13
#print axioms R1Z.PV_Inv_MaskChunk0.block_14
#print axioms R1Z.PV_Inv_MaskChunk0.block_15
#print axioms R1Z.PV_Inv_MaskChunk1.block_16
#print axioms R1Z.PV_Inv_MaskChunk1.block_17
#print axioms R1Z.PV_Inv_MaskChunk1.block_18
#print axioms R1Z.PV_Inv_MaskChunk1.block_19
#print axioms R1Z.PV_Inv_MaskChunk1.block_20
#print axioms R1Z.PV_Inv_MaskChunk1.block_21
#print axioms R1Z.PV_Inv_MaskChunk1.block_22
#print axioms R1Z.PV_Inv_MaskChunk1.block_23
#print axioms R1Z.PV_Inv_MaskChunk1.block_24
#print axioms R1Z.PV_Inv_MaskChunk1.block_25
#print axioms R1Z.PV_Inv_MaskChunk1.block_26
#print axioms R1Z.PV_Inv_MaskChunk1.block_27
#print axioms R1Z.PV_Inv_MaskChunk1.block_28
#print axioms R1Z.PV_Inv_MaskChunk1.block_29
#print axioms R1Z.PV_Inv_MaskChunk1.block_30
#print axioms R1Z.PV_Inv_MaskChunk1.block_31
#print axioms R1Z.PV_Inv_MaskChunk2.block_32
#print axioms R1Z.PV_Inv_MaskChunk2.block_33
#print axioms R1Z.PV_Inv_MaskChunk2.block_34
#print axioms R1Z.PV_Inv_MaskChunk2.block_35
#print axioms R1Z.PV_Inv_MaskChunk2.block_36
#print axioms R1Z.PV_Inv_MaskChunk2.block_37
#print axioms R1Z.PV_Inv_MaskChunk2.block_38
#print axioms R1Z.PV_Inv_MaskChunk2.block_39
#print axioms R1Z.PV_Inv_MaskChunk2.block_40
#print axioms R1Z.PV_Inv_MaskChunk2.block_41
#print axioms R1Z.PV_Inv_MaskChunk2.block_42
#print axioms R1Z.PV_Inv_MaskChunk2.block_43
#print axioms R1Z.PV_Inv_MaskChunk2.block_44
#print axioms R1Z.PV_Inv_MaskChunk2.block_45
#print axioms R1Z.PV_Inv_MaskChunk2.block_46
#print axioms R1Z.PV_Inv_MaskChunk2.block_47
#print axioms R1Z.PV_Inv_MaskPartition.fold_initial
#print axioms R1Z.PV_Inv_MaskPartition.append
#print axioms R1Z.PV_Inv_MaskPartition.decomposition
#print axioms R1Z.PV_Inv_MaskSource.rows_active
#print axioms R1Z.PV_Inv_NativeTupleJoin.input_join
#print axioms R1Z.PV_Inv_PackedInverseList.native_inverses
#print axioms R1Z.PV_Inv_PackedNormSafety.norms_at_slot
#print axioms R1Z.PV_Inv_PreGuard.source_equation
#print axioms R1Z.PV_Inv_RawBankList.exact_reads
#print axioms R1Z.PV_Inv_RawBankRead.exact_read
#print axioms R1Z.PV_Inv_RawBankTuple.tuple_read
#print axioms R1Z.PV_Inv_RegistryFamilyEight.eight_attempts
#print axioms R1Z.PV_Inv_RegistryFamilyEvent.contained
#print axioms R1Z.PV_Inv_RegistryFamilyMass.one_attempt
#print axioms R1Z.PV_Inv_RegistryInput.member
#print axioms R1Z.PV_Inv_RegistryPacking.reached_nonzero
#print axioms R1Z.PV_Inv_RegistryZeroEvent.contained
#print axioms R1Z.PV_Inv_SourceConsumerJoin.source_inverse
#print axioms R1Z.PV_Inv_SourceProducerJoin.source_inverse
#print axioms R1Z.PV_Inv_TagWord.embed_nat
#print axioms R1Z.PV_Inv_TagWord.source_tag
#print axioms R1Z.PV_Inv_TaggedBank.source_equation
#print axioms R1Z.PV_Inv_TripleNorm.nonzero_tower
