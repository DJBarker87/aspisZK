import NGK_COMBINED_IMPORT
import NIU_COMBINED_IMPORT
import NJB_COMBINED_IMPORT
import NIX_ResidualCut
import NIX_ResidualLog
import NJL_AbsorptionInvocation
import NJL_AbsorptionPrologue
import NJL_ActiveInvocation
import NJL_ArrayCodec
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
import NJL_OccupancyTail
import NJL_PathAssociation
import NJL_PathContext
import NJL_PathFrame
import NJL_PathPacket
import NJL_PathStep
import NJL_PathTrace
import NJL_Traverse
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
#check AspisR1.NJL_PathStep.domain
#print axioms AspisR1.NJL_PathStep.domain
#check AspisR1.NJL_PathStep.source
#print axioms AspisR1.NJL_PathStep.source
#check AspisR1.NJL_PathTrace.source
#print axioms AspisR1.NJL_PathTrace.source
#check AspisR1.NJL_Traverse.packet
#print axioms AspisR1.NJL_Traverse.packet
#check AspisR1.NJL_WriteFrame.fold
#print axioms AspisR1.NJL_WriteFrame.fold
#check AspisR1.NIX_ResidualCut.packet
#print axioms AspisR1.NIX_ResidualCut.packet
#check AspisR1.NIX_ResidualLog.packet
#print axioms AspisR1.NIX_ResidualLog.packet
#check AspisR1.NJB_SemanticPublic.result
#print axioms AspisR1.NJB_SemanticPublic.result
