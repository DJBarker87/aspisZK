-- Final focused import/axiom audit; no package or frozen-manifest replay.
import PoolS2_ChronologyCodes
import PoolS2_Count
import PoolS2_EntryMaster
import PoolS2_Index
import PoolS2_Instruction
import PoolS2_InstructionSource
import PoolS2_KeyExact
import PoolS2_KeyLoop
import PoolS2_KeyStep
import PoolS2_KeySuffix
import PoolS2_LaneFacts
import PoolS2_Lanes
import PoolS2_MasterCuts
import PoolS2_MasterErrors
import PoolS2_MasterFacts
import PoolS2_MasterRead
import PoolS2_MasterStage
import PoolS2_MasterValidExact
import PoolS2_MasterValidFacts
import PoolS2_MasterValidation
import PoolS2_NextValid
import PoolS2_Payer
import PoolS2_PayerExact
import PoolS2_PdaCheckpoint
import PoolS2_PdaLane
import PoolS2_PdaLaneAccepted
import PoolS2_PdaLaneFind
import PoolS2_PdaMaster
import PoolS2_PdaPrimitives
import PoolS2_PdaSeeds
import PoolS2_PdaSource
import PoolS2_PlannerBindings
import PoolS2_PlannerChronology
import PoolS2_PlannerCuts
import PoolS2_PlannerExact
import PoolS2_PlannerFacts
import PoolS2_PlannerFirst
import PoolS2_PlannerIndices
import PoolS2_PlannerModel
import PoolS2_PlannerReady
import PoolS2_PolicyExact
import PoolS2_PolicyFacts
import PoolS2_PolicySource
import PoolS2_Prefix
import PoolS2_PrefixCuts
import PoolS2_PrefixFacts
import PoolS2_PrefixKeys
import PoolS2_PrefixSource
import PoolS2_PrefixUnique
import PoolS2_Ranges
import PoolS2_RawMaster
import PoolS2_RawPrefix
import PoolS2_RawSnapshot
import PoolS2_RightExact
import PoolS2_RightLoop
import PoolS2_RightStep
import PoolS2_RightSuffix
import PoolS2_SelectCuts
import PoolS2_SelectedLanes
import PoolS2_StagePrefix
import PoolS2_UniqueExact
import PoolS2_UniqueLoop
import PoolS2_UniqueRoles
import PoolS2_UniqueSource
import PoolS2_UniqueStep
import PoolS2_UniqueSuffix
import PoolT_Write
set_option autoImplicit false
#print axioms AspisR1.PoolS2_ChronologyCodes.codes
#print axioms AspisR1.PoolS2_ChronologyCodes.accepted_code
#print axioms AspisR1.PoolS2_Count.accepted
#print axioms AspisR1.PoolS2_Count.short
#print axioms AspisR1.PoolS2_Count.long
#print axioms AspisR1.PoolS2_EntryMaster.accepted
#print axioms AspisR1.PoolS2_Index.increment
#print axioms AspisR1.PoolS2_Index.read
#print axioms AspisR1.PoolS2_Instruction.encoded
#print axioms AspisR1.PoolS2_Instruction.accepted
#print axioms AspisR1.PoolS2_Instruction.wrong_length
#print axioms AspisR1.PoolS2_InstructionSource.pair_forest.encode_pair_forest_checkpoint_instruction_v1
#print axioms AspisR1.PoolS2_InstructionSource.pair_forest.decode_pair_forest_checkpoint_instruction_v1
#print axioms AspisR1.PoolS2_KeyExact.zip_equal
#print axioms AspisR1.PoolS2_KeyExact.exact
#print axioms AspisR1.PoolS2_KeyLoop.exact
#print axioms AspisR1.PoolS2_KeyStep.step
#print axioms AspisR1.PoolS2_KeyStep.stopped
#print axioms AspisR1.PoolS2_KeyStep.ended
#print axioms AspisR1.PoolS2_KeySuffix.cons_pairs
#print axioms AspisR1.PoolS2_KeySuffix.next
#print axioms AspisR1.PoolS2_KeySuffix.ended
#print axioms AspisR1.PoolS2_LaneFacts.accepted_iff
#print axioms AspisR1.PoolS2_LaneFacts.bounds
#print axioms AspisR1.PoolS2_Lanes.sequence_list
#print axioms AspisR1.PoolS2_Lanes.sequence_length
#print axioms AspisR1.PoolS2_MasterCuts.accepted
#print axioms AspisR1.PoolS2_MasterErrors.metadata_error
#print axioms AspisR1.PoolS2_MasterErrors.signer_error
#print axioms AspisR1.PoolS2_MasterErrors.read_error
#print axioms AspisR1.PoolS2_MasterErrors.decoder_error
#print axioms AspisR1.PoolS2_MasterFacts.accepted
#print axioms AspisR1.PoolS2_MasterRead.run
#print axioms AspisR1.PoolS2_MasterStage.accepted
#print axioms AspisR1.PoolS2_MasterValidExact.ready
#print axioms AspisR1.PoolS2_MasterValidExact.accepted_iff
#print axioms AspisR1.PoolS2_MasterValidFacts.accepted
#print axioms AspisR1.PoolS2_MasterValidation.run
#print axioms AspisR1.PoolS2_NextValid.derived
#print axioms AspisR1.PoolS2_Payer.accepted
#print axioms AspisR1.PoolS2_PayerExact.ready
#print axioms AspisR1.PoolS2_PayerExact.accepted_iff
#print axioms AspisR1.PoolS2_PdaCheckpoint.exact
#print axioms AspisR1.PoolS2_PdaCheckpoint.returned
#print axioms AspisR1.PoolS2_PdaLane.widen
#print axioms AspisR1.PoolS2_PdaLane.valid
#print axioms AspisR1.PoolS2_PdaLane.invalid
#print axioms AspisR1.PoolS2_PdaLane.accepted_bound
#print axioms AspisR1.PoolS2_PdaLaneAccepted.accepted
#print axioms AspisR1.PoolS2_PdaLaneAccepted.accepted_iff
#print axioms AspisR1.PoolS2_PdaLaneAccepted.create_error
#print axioms AspisR1.PoolS2_PdaLaneFind.valid
#print axioms AspisR1.PoolS2_PdaLaneFind.invalid
#print axioms AspisR1.PoolS2_PdaLaneFind.returned
#print axioms AspisR1.PoolS2_PdaMaster.matched_exact
#print axioms AspisR1.PoolS2_PdaMaster.accepted
#print axioms AspisR1.PoolS2_PdaMaster.accepted_iff
#print axioms AspisR1.PoolS2_PdaMaster.find_exact
#print axioms AspisR1.PoolS2_PdaPrimitives.accepted
#print axioms AspisR1.PoolS2_PdaPrimitives.ready
#print axioms AspisR1.PoolS2_PdaPrimitives.rejected
#print axioms AspisR1.PoolS2_PdaPrimitives.failed
#print axioms AspisR1.PoolS2_PdaPrimitives.diverged
#print axioms AspisR1.PoolS2_PdaSeeds.master_prefix
#print axioms AspisR1.PoolS2_PdaSeeds.lane_prefix
#print axioms AspisR1.PoolS2_PdaSeeds.checkpoint_prefix
#print axioms AspisR1.PoolS2_PdaSeeds.key_bytes
#print axioms AspisR1.PoolS2_PdaSeeds.one_byte
#print axioms AspisR1.PoolS2_PdaSeeds.sequence_bytes
#print axioms AspisR1.PoolS2_PdaSource.registry.stored_bump_address_matches
#print axioms AspisR1.PoolS2_PdaSource.pair_forest.master_address_matches
#print axioms AspisR1.PoolS2_PdaSource.pair_forest.lane_address_matches
#print axioms AspisR1.PoolS2_PdaSource.pair_forest.pool_v1_pair_forest_checkpoint_address
#print axioms AspisR1.PoolS2_PlannerBindings.accepted
#print axioms AspisR1.PoolS2_PlannerChronology.increment
#print axioms AspisR1.PoolS2_PlannerChronology.repeated
#print axioms AspisR1.PoolS2_PlannerCuts.accepted
#print axioms AspisR1.PoolS2_PlannerExact.accepted_iff
#print axioms AspisR1.PoolS2_PlannerFacts.accepted
#print axioms AspisR1.PoolS2_PlannerFirst.accepted
#print axioms AspisR1.PoolS2_PlannerIndices.accepted
#print axioms AspisR1.PoolS2_PlannerModel.run
#print axioms AspisR1.PoolS2_PlannerReady.ready
#print axioms AspisR1.PoolS2_PolicyExact.ready
#print axioms AspisR1.PoolS2_PolicyExact.accepted_iff
#print axioms AspisR1.PoolS2_PolicyFacts.accepted
#print axioms AspisR1.PoolS2_PolicySource.pool_v1.format.validate_verifier_policy_v1
#print axioms AspisR1.PoolS2_Prefix.unique
#print axioms AspisR1.PoolS2_Prefix.select
#print axioms AspisR1.PoolS2_Prefix.run
#print axioms AspisR1.PoolS2_PrefixCuts.accepted
#print axioms AspisR1.PoolS2_PrefixFacts.accepted
#print axioms AspisR1.PoolS2_PrefixKeys.selected_key
#print axioms AspisR1.PoolS2_PrefixKeys.master_checkpoint
#print axioms AspisR1.PoolS2_PrefixSource.pair_forest.require_exact_account_count
#print axioms AspisR1.PoolS2_PrefixSource.processor.require_payer_and_system_program
#print axioms AspisR1.PoolS2_PrefixUnique.accepted
#print axioms AspisR1.PoolS2_PrefixUnique.keys_count
#print axioms AspisR1.PoolS2_Ranges.selected_exact
#print axioms AspisR1.PoolS2_Ranges.selected_exists
#print axioms AspisR1.PoolS2_Ranges.indexed
#print axioms AspisR1.PoolS2_RawMaster.accepted
#print axioms AspisR1.PoolS2_RawPrefix.roles
#print axioms AspisR1.PoolS2_RawPrefix.data_cells
#print axioms AspisR1.PoolS2_RawSnapshot.count
#print axioms AspisR1.PoolS2_RawSnapshot.raw
#print axioms AspisR1.PoolS2_RawSnapshot.metadata
#print axioms AspisR1.PoolS2_RawSnapshot.indexed
#print axioms AspisR1.PoolS2_RawSnapshot.cell_alias
#print axioms AspisR1.PoolS2_RightExact.exact
#print axioms AspisR1.PoolS2_RightLoop.exact
#print axioms AspisR1.PoolS2_RightStep.step
#print axioms AspisR1.PoolS2_RightStep.stopped
#print axioms AspisR1.PoolS2_RightStep.ended
#print axioms AspisR1.PoolS2_RightSuffix.next
#print axioms AspisR1.PoolS2_RightSuffix.ended
#print axioms AspisR1.PoolS2_SelectCuts.accepted
#print axioms AspisR1.PoolS2_SelectedLanes.selected
#print axioms AspisR1.PoolS2_SelectedLanes.accepted
#print axioms AspisR1.PoolS2_StagePrefix.accepted
#print axioms AspisR1.PoolS2_UniqueExact.exact
#print axioms AspisR1.PoolS2_UniqueExact.accepted
#print axioms AspisR1.PoolS2_UniqueExact.rejected
#print axioms AspisR1.PoolS2_UniqueLoop.exact
#print axioms AspisR1.PoolS2_UniqueRoles.ordered
#print axioms AspisR1.PoolS2_UniqueRoles.checkpoint_master
#print axioms PoolS2_Unique.PoolS2_Unique.key_equal
#print axioms PoolS2_Unique.PoolS2_Unique.right_unique
#print axioms PoolS2_Unique.PoolS2_Unique.unique_keys
#print axioms AspisR1.PoolS2_UniqueStep.step
#print axioms AspisR1.PoolS2_UniqueStep.stopped
#print axioms AspisR1.PoolS2_UniqueStep.ended
#print axioms AspisR1.PoolS2_UniqueSuffix.row_decide
#print axioms AspisR1.PoolS2_UniqueSuffix.next
#print axioms AspisR1.PoolS2_UniqueSuffix.ended
#print axioms AspisR1.PoolT_Write.accepted_verifier_writes_copy
