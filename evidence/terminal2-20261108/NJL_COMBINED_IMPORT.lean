import NGK_COMBINED_IMPORT
import NIU_COMBINED_IMPORT
import NJB_COMBINED_IMPORT
import NIX_ResidualCut
import NIX_ResidualLog
import NJL_AbsorptionInvocation
import NJL_AbsorptionPrologue
import NJL_ActiveInvocation
import NJL_ArrayCodec
import NJL_CacheReads
import NJL_CachedPowers
import NJL_CachedWindow
import NJL_EndpointCell
import NJL_EndpointIndices
import NJL_EndpointLookup
import NJL_EndpointRoot
import NJL_EndpointWrites
import NJL_LowDischarge
import NJL_OccupancyAssociation
import NJL_OccupancyContext
import NJL_OccupancyFrame
import NJL_OccupancyHead
import NJL_OccupancyLanes
import NJL_OccupancyPacket
import NJL_OccupancyParent
import NJL_OccupancyTail
import NJL_PathAssociation
import NJL_PathContext
import NJL_PathFrame
import NJL_PathPacket
import NJL_PathParent
import NJL_PathSelector
import NJL_PathStep
import NJL_PathTrace
import NJL_PatternCuts
import NJL_PatternInner
import NJL_PatternMeaning
import NJL_PatternOuter
import NJL_PatternRoot
import NJL_SharedCuts
import NJL_SharedMeaning
import NJL_SharedRoot
import NJL_SharedTrace
import NJL_TagChunk
import NJL_TagChunk00
import NJL_TagChunk01
import NJL_TagChunk02
import NJL_TagChunk03
import NJL_TagChunk04
import NJL_TagChunk05
import NJL_TagChunk06
import NJL_TagChunk07
import NJL_TagChunks
import NJL_TagData
import NJL_TagForward
import NJL_TagMeaning
import NJL_TagPartition
import NJL_TagRawStep
import NJL_TagRawTrace
import NJL_TagReduction
import NJL_TagRoot
import NJL_TagSchedule
import NJL_TagWords
import NJL_Traverse
import NJL_WindowCache
import NJL_WindowFold
import NJL_WindowPowerArray
import NJL_WindowPowerFrame
import NJL_WindowPowerOverwrite
import NJL_WindowPowers
import NJL_WindowStep
import NJL_WriteFrame

#print axioms AspisR1.RPx_Deployed.deployed
#check AspisR1.NJL_AbsorptionInvocation.lanes
#print axioms AspisR1.NJL_AbsorptionInvocation.lanes
#check AspisR1.NJL_AbsorptionInvocation.source
#print axioms AspisR1.NJL_AbsorptionInvocation.source
#check AspisR1.NJL_AbsorptionPrologue.source
#print axioms AspisR1.NJL_AbsorptionPrologue.source
#check AspisR1.NJL_ActiveInvocation.high_run
#print axioms AspisR1.NJL_ActiveInvocation.high_run
#check AspisR1.NJL_ActiveInvocation.high_step
#print axioms AspisR1.NJL_ActiveInvocation.high_step
#check AspisR1.NJL_ActiveInvocation.low_run
#print axioms AspisR1.NJL_ActiveInvocation.low_run
#check AspisR1.NJL_ActiveInvocation.low_step
#print axioms AspisR1.NJL_ActiveInvocation.low_step
#check AspisR1.NJL_ActiveInvocation.source
#print axioms AspisR1.NJL_ActiveInvocation.source
#check AspisR1.NJL_ArrayCodec.ext
#print axioms AspisR1.NJL_ArrayCodec.ext
#check AspisR1.NJL_CacheReads.canonical
#print axioms AspisR1.NJL_CacheReads.canonical
#check AspisR1.NJL_CacheReads.constructor
#print axioms AspisR1.NJL_CacheReads.constructor
#check AspisR1.NJL_CacheReads.paired
#print axioms AspisR1.NJL_CacheReads.paired
#check AspisR1.NJL_CacheReads.value
#print axioms AspisR1.NJL_CacheReads.value
#check AspisR1.NJL_CachedPowers.source
#print axioms AspisR1.NJL_CachedPowers.source
#check AspisR1.NJL_CachedWindow.source
#print axioms AspisR1.NJL_CachedWindow.source
#check AspisR1.NJL_EndpointCell.source
#print axioms AspisR1.NJL_EndpointCell.source
#check AspisR1.NJL_EndpointIndices.disjoint
#print axioms AspisR1.NJL_EndpointIndices.disjoint
#check AspisR1.NJL_EndpointIndices.pattern_domain
#print axioms AspisR1.NJL_EndpointIndices.pattern_domain
#check AspisR1.NJL_EndpointIndices.weight_domain
#print axioms AspisR1.NJL_EndpointIndices.weight_domain
#check AspisR1.NJL_EndpointLookup.block_shift
#print axioms AspisR1.NJL_EndpointLookup.block_shift
#check AspisR1.NJL_EndpointLookup.caller_weight
#print axioms AspisR1.NJL_EndpointLookup.caller_weight
#check AspisR1.NJL_EndpointLookup.group_unique
#print axioms AspisR1.NJL_EndpointLookup.group_unique
#check AspisR1.NJL_EndpointLookup.high_canonical
#print axioms AspisR1.NJL_EndpointLookup.high_canonical
#check AspisR1.NJL_EndpointLookup.member
#print axioms AspisR1.NJL_EndpointLookup.member
#check AspisR1.NJL_EndpointLookup.pattern_unique
#print axioms AspisR1.NJL_EndpointLookup.pattern_unique
#check AspisR1.NJL_EndpointLookup.scan_step
#print axioms AspisR1.NJL_EndpointLookup.scan_step
#check AspisR1.NJL_EndpointLookup.size136
#print axioms AspisR1.NJL_EndpointLookup.size136
#check AspisR1.NJL_EndpointRoot.selected_value
#print axioms AspisR1.NJL_EndpointRoot.selected_value
#check AspisR1.NJL_EndpointRoot.source
#print axioms AspisR1.NJL_EndpointRoot.source
#check AspisR1.NJL_EndpointWrites.selected_call
#print axioms AspisR1.NJL_EndpointWrites.selected_call
#check AspisR1.NJL_EndpointWrites.selected_canonical
#print axioms AspisR1.NJL_EndpointWrites.selected_canonical
#check AspisR1.NJL_EndpointWrites.source
#print axioms AspisR1.NJL_EndpointWrites.source
#check AspisR1.NJL_LowDischarge.source
#print axioms AspisR1.NJL_LowDischarge.source
#check AspisR1.NJL_OccupancyAssociation.cell_value
#print axioms AspisR1.NJL_OccupancyAssociation.cell_value
#check AspisR1.NJL_OccupancyAssociation.source
#print axioms AspisR1.NJL_OccupancyAssociation.source
#check AspisR1.NJL_OccupancyAssociation.value
#print axioms AspisR1.NJL_OccupancyAssociation.value
#check AspisR1.NJL_OccupancyContext.source
#print axioms AspisR1.NJL_OccupancyContext.source
#check AspisR1.NJL_OccupancyFrame.full_mem
#print axioms AspisR1.NJL_OccupancyFrame.full_mem
#check AspisR1.NJL_OccupancyFrame.input_same
#print axioms AspisR1.NJL_OccupancyFrame.input_same
#check AspisR1.NJL_OccupancyFrame.model_run
#print axioms AspisR1.NJL_OccupancyFrame.model_run
#check AspisR1.NJL_OccupancyFrame.model_step
#print axioms AspisR1.NJL_OccupancyFrame.model_step
#check AspisR1.NJL_OccupancyFrame.source
#print axioms AspisR1.NJL_OccupancyFrame.source
#check AspisR1.NJL_OccupancyHead.source
#print axioms AspisR1.NJL_OccupancyHead.source
#check AspisR1.NJL_OccupancyLanes.source
#print axioms AspisR1.NJL_OccupancyLanes.source
#check AspisR1.NJL_OccupancyLanes.step
#print axioms AspisR1.NJL_OccupancyLanes.step
#check AspisR1.NJL_OccupancyPacket.pack_decode
#print axioms AspisR1.NJL_OccupancyPacket.pack_decode
#check AspisR1.NJL_OccupancyPacket.size12
#print axioms AspisR1.NJL_OccupancyPacket.size12
#check AspisR1.NJL_OccupancyPacket.source
#print axioms AspisR1.NJL_OccupancyPacket.source
#check AspisR1.NJL_OccupancyParent.source
#print axioms AspisR1.NJL_OccupancyParent.source
#check AspisR1.NJL_OccupancyTail.source
#print axioms AspisR1.NJL_OccupancyTail.source
#check AspisR1.NJL_PathAssociation.source
#print axioms AspisR1.NJL_PathAssociation.source
#check AspisR1.NJL_PathAssociation.value
#print axioms AspisR1.NJL_PathAssociation.value
#check AspisR1.NJL_PathContext.source
#print axioms AspisR1.NJL_PathContext.source
#check AspisR1.NJL_PathFrame.full_mem
#print axioms AspisR1.NJL_PathFrame.full_mem
#check AspisR1.NJL_PathFrame.look_fin
#print axioms AspisR1.NJL_PathFrame.look_fin
#check AspisR1.NJL_PathFrame.model_run
#print axioms AspisR1.NJL_PathFrame.model_run
#check AspisR1.NJL_PathFrame.source
#print axioms AspisR1.NJL_PathFrame.source
#check AspisR1.NJL_PathFrame.target_value
#print axioms AspisR1.NJL_PathFrame.target_value
#check AspisR1.NJL_PathPacket.pack_decode
#print axioms AspisR1.NJL_PathPacket.pack_decode
#check AspisR1.NJL_PathPacket.size17
#print axioms AspisR1.NJL_PathPacket.size17
#check AspisR1.NJL_PathPacket.source
#print axioms AspisR1.NJL_PathPacket.source
#check AspisR1.NJL_PathParent.source
#print axioms AspisR1.NJL_PathParent.source
#check AspisR1.NJL_PathSelector.source
#print axioms AspisR1.NJL_PathSelector.source
#check AspisR1.NJL_PathStep.domain
#print axioms AspisR1.NJL_PathStep.domain
#check AspisR1.NJL_PathStep.source
#print axioms AspisR1.NJL_PathStep.source
#check AspisR1.NJL_PathTrace.source
#print axioms AspisR1.NJL_PathTrace.source
#check AspisR1.NJL_PatternCuts.inner_source
#print axioms AspisR1.NJL_PatternCuts.inner_source
#check AspisR1.NJL_PatternCuts.outer_source
#print axioms AspisR1.NJL_PatternCuts.outer_source
#check AspisR1.NJL_PatternInner.run
#print axioms AspisR1.NJL_PatternInner.run
#check AspisR1.NJL_PatternInner.source
#print axioms AspisR1.NJL_PatternInner.source
#check AspisR1.NJL_PatternMeaning.fold_prefix
#print axioms AspisR1.NJL_PatternMeaning.fold_prefix
#check AspisR1.NJL_PatternMeaning.value
#print axioms AspisR1.NJL_PatternMeaning.value
#check AspisR1.NJL_PatternOuter.group_source
#print axioms AspisR1.NJL_PatternOuter.group_source
#check AspisR1.NJL_PatternOuter.run
#print axioms AspisR1.NJL_PatternOuter.run
#check AspisR1.NJL_PatternOuter.source
#print axioms AspisR1.NJL_PatternOuter.source
#check AspisR1.NJL_PatternRoot.source
#print axioms AspisR1.NJL_PatternRoot.source
#check AspisR1.NJL_SharedCuts.source
#print axioms AspisR1.NJL_SharedCuts.source
#check AspisR1.NJL_SharedMeaning.contribution
#print axioms AspisR1.NJL_SharedMeaning.contribution
#check AspisR1.NJL_SharedMeaning.fold_prefix
#print axioms AspisR1.NJL_SharedMeaning.fold_prefix
#check AspisR1.NJL_SharedMeaning.group_injective
#print axioms AspisR1.NJL_SharedMeaning.group_injective
#check AspisR1.NJL_SharedMeaning.lane
#print axioms AspisR1.NJL_SharedMeaning.lane
#check AspisR1.NJL_SharedMeaning.outside
#print axioms AspisR1.NJL_SharedMeaning.outside
#check AspisR1.NJL_SharedMeaning.value
#print axioms AspisR1.NJL_SharedMeaning.value
#check AspisR1.NJL_SharedRoot.source
#print axioms AspisR1.NJL_SharedRoot.source
#check AspisR1.NJL_SharedTrace.source
#print axioms AspisR1.NJL_SharedTrace.source
#check AspisR1.NJL_TagChunk.source
#print axioms AspisR1.NJL_TagChunk.source
#check AspisR1.NJL_TagChunk00.block_all
#print axioms AspisR1.NJL_TagChunk00.block_all
#check AspisR1.NJL_TagChunk00.block_length
#print axioms AspisR1.NJL_TagChunk00.block_length
#check AspisR1.NJL_TagChunk00.tag_all
#print axioms AspisR1.NJL_TagChunk00.tag_all
#check AspisR1.NJL_TagChunk00.tag_length
#print axioms AspisR1.NJL_TagChunk00.tag_length
#check AspisR1.NJL_TagChunk01.block_all
#print axioms AspisR1.NJL_TagChunk01.block_all
#check AspisR1.NJL_TagChunk01.block_length
#print axioms AspisR1.NJL_TagChunk01.block_length
#check AspisR1.NJL_TagChunk01.tag_all
#print axioms AspisR1.NJL_TagChunk01.tag_all
#check AspisR1.NJL_TagChunk01.tag_length
#print axioms AspisR1.NJL_TagChunk01.tag_length
#check AspisR1.NJL_TagChunk02.block_all
#print axioms AspisR1.NJL_TagChunk02.block_all
#check AspisR1.NJL_TagChunk02.block_length
#print axioms AspisR1.NJL_TagChunk02.block_length
#check AspisR1.NJL_TagChunk02.tag_all
#print axioms AspisR1.NJL_TagChunk02.tag_all
#check AspisR1.NJL_TagChunk02.tag_length
#print axioms AspisR1.NJL_TagChunk02.tag_length
#check AspisR1.NJL_TagChunk03.block_all
#print axioms AspisR1.NJL_TagChunk03.block_all
#check AspisR1.NJL_TagChunk03.block_length
#print axioms AspisR1.NJL_TagChunk03.block_length
#check AspisR1.NJL_TagChunk03.tag_all
#print axioms AspisR1.NJL_TagChunk03.tag_all
#check AspisR1.NJL_TagChunk03.tag_length
#print axioms AspisR1.NJL_TagChunk03.tag_length
#check AspisR1.NJL_TagChunk04.block_all
#print axioms AspisR1.NJL_TagChunk04.block_all
#check AspisR1.NJL_TagChunk04.block_length
#print axioms AspisR1.NJL_TagChunk04.block_length
#check AspisR1.NJL_TagChunk04.tag_all
#print axioms AspisR1.NJL_TagChunk04.tag_all
#check AspisR1.NJL_TagChunk04.tag_length
#print axioms AspisR1.NJL_TagChunk04.tag_length
#check AspisR1.NJL_TagChunk05.block_all
#print axioms AspisR1.NJL_TagChunk05.block_all
#check AspisR1.NJL_TagChunk05.block_length
#print axioms AspisR1.NJL_TagChunk05.block_length
#check AspisR1.NJL_TagChunk05.tag_all
#print axioms AspisR1.NJL_TagChunk05.tag_all
#check AspisR1.NJL_TagChunk05.tag_length
#print axioms AspisR1.NJL_TagChunk05.tag_length
#check AspisR1.NJL_TagChunk06.block_all
#print axioms AspisR1.NJL_TagChunk06.block_all
#check AspisR1.NJL_TagChunk06.block_length
#print axioms AspisR1.NJL_TagChunk06.block_length
#check AspisR1.NJL_TagChunk06.tag_all
#print axioms AspisR1.NJL_TagChunk06.tag_all
#check AspisR1.NJL_TagChunk06.tag_length
#print axioms AspisR1.NJL_TagChunk06.tag_length
#check AspisR1.NJL_TagChunk07.block_all
#print axioms AspisR1.NJL_TagChunk07.block_all
#check AspisR1.NJL_TagChunk07.block_length
#print axioms AspisR1.NJL_TagChunk07.block_length
#check AspisR1.NJL_TagChunk07.tag_all
#print axioms AspisR1.NJL_TagChunk07.tag_all
#check AspisR1.NJL_TagChunk07.tag_length
#print axioms AspisR1.NJL_TagChunk07.tag_length
#check AspisR1.NJL_TagChunks.dot_append
#print axioms AspisR1.NJL_TagChunks.dot_append
#check AspisR1.NJL_TagChunks.source
#print axioms AspisR1.NJL_TagChunks.source
#check AspisR1.NJL_TagData.block_all
#print axioms AspisR1.NJL_TagData.block_all
#check AspisR1.NJL_TagData.block_length
#print axioms AspisR1.NJL_TagData.block_length
#check AspisR1.NJL_TagData.interval
#print axioms AspisR1.NJL_TagData.interval
#check AspisR1.NJL_TagData.range_values
#print axioms AspisR1.NJL_TagData.range_values
#check AspisR1.NJL_TagData.tag_all
#print axioms AspisR1.NJL_TagData.tag_all
#check AspisR1.NJL_TagData.tag_bound
#print axioms AspisR1.NJL_TagData.tag_bound
#check AspisR1.NJL_TagData.tag_length
#print axioms AspisR1.NJL_TagData.tag_length
#check AspisR1.NJL_TagForward.source
#print axioms AspisR1.NJL_TagForward.source
#check AspisR1.NJL_TagMeaning.encode_add
#print axioms AspisR1.NJL_TagMeaning.encode_add
#check AspisR1.NJL_TagMeaning.encode_decode
#print axioms AspisR1.NJL_TagMeaning.encode_decode
#check AspisR1.NJL_TagMeaning.encode_zero
#print axioms AspisR1.NJL_TagMeaning.encode_zero
#check AspisR1.NJL_TagMeaning.residue
#print axioms AspisR1.NJL_TagMeaning.residue
#check AspisR1.NJL_TagMeaning.scalar
#print axioms AspisR1.NJL_TagMeaning.scalar
#check AspisR1.NJL_TagMeaning.value
#print axioms AspisR1.NJL_TagMeaning.value
#check AspisR1.NJL_TagPartition.coordinate
#print axioms AspisR1.NJL_TagPartition.coordinate
#check AspisR1.NJL_TagPartition.flatten
#print axioms AspisR1.NJL_TagPartition.flatten
#check AspisR1.NJL_TagPartition.small
#print axioms AspisR1.NJL_TagPartition.small
#check AspisR1.NJL_TagRawStep.add
#print axioms AspisR1.NJL_TagRawStep.add
#check AspisR1.NJL_TagRawStep.source
#print axioms AspisR1.NJL_TagRawStep.source
#check AspisR1.NJL_TagRawTrace.source
#print axioms AspisR1.NJL_TagRawTrace.source
#check AspisR1.NJL_TagReduction.source
#print axioms AspisR1.NJL_TagReduction.source
#check AspisR1.NJL_TagReduction.step_source
#print axioms AspisR1.NJL_TagReduction.step_source
#check AspisR1.NJL_TagRoot.source
#print axioms AspisR1.NJL_TagRoot.source
#check AspisR1.NJL_TagSchedule.chunk
#print axioms AspisR1.NJL_TagSchedule.chunk
#check AspisR1.NJL_TagSchedule.coordinate
#print axioms AspisR1.NJL_TagSchedule.coordinate
#check AspisR1.NJL_TagSchedule.source
#print axioms AspisR1.NJL_TagSchedule.source
#check AspisR1.NJL_TagWords.cast64
#print axioms AspisR1.NJL_TagWords.cast64
#check AspisR1.NJL_TagWords.domain
#print axioms AspisR1.NJL_TagWords.domain
#check AspisR1.NJL_TagWords.product
#print axioms AspisR1.NJL_TagWords.product
#check AspisR1.NJL_TagWords.word_bound
#print axioms AspisR1.NJL_TagWords.word_bound
#check AspisR1.NJL_Traverse.packet
#print axioms AspisR1.NJL_Traverse.packet
#check AspisR1.NJL_WindowCache.source
#print axioms AspisR1.NJL_WindowCache.source
#check AspisR1.NJL_WindowFold.source
#print axioms AspisR1.NJL_WindowFold.source
#check AspisR1.NJL_WindowPowerArray.source
#print axioms AspisR1.NJL_WindowPowerArray.source
#check AspisR1.NJL_WindowPowerFrame.lift
#print axioms AspisR1.NJL_WindowPowerFrame.lift
#check AspisR1.NJL_WindowPowerOverwrite.overwrite
#print axioms AspisR1.NJL_WindowPowerOverwrite.overwrite
#check AspisR1.NJL_WindowPowerOverwrite.power_list
#print axioms AspisR1.NJL_WindowPowerOverwrite.power_list
#check AspisR1.NJL_WindowPowers.source
#print axioms AspisR1.NJL_WindowPowers.source
#check AspisR1.NJL_WindowStep.source
#print axioms AspisR1.NJL_WindowStep.source
#check AspisR1.NJL_WriteFrame.fold
#print axioms AspisR1.NJL_WriteFrame.fold
#check AspisR1.NIX_ResidualCut.packet
#print axioms AspisR1.NIX_ResidualCut.packet
#check AspisR1.NIX_ResidualLog.packet
#print axioms AspisR1.NIX_ResidualLog.packet
#check AspisR1.NJB_SemanticPublic.result
#print axioms AspisR1.NJB_SemanticPublic.result
