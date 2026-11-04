-- Standalone NFC forest; joint headline import failed in NFC_L058.
import NFC_AddDomain
import NFC_ArrayFour
import NFE_NFC_CalleeDomains
import NFE_NFC_ChainAssociation
import NFC_CheckedArithmetic
import NFE_NFC_DotDomain
import NFE_NFC_DotPushCut
import NFE_NFC_DotPushFour
import NFE_NFC_DotPushStep
import NFE_NFC_DotPushTotal
import NFE_NFC_DotWordStep
import NFE_NFC_FinalCalls
import NFE_NFC_FirstGeometry
import NFE_NFC_FirstJoin
import NFE_NFC_FirstSource
import NFE_NFC_FourDomain
import NFE_NFC_HeadDomain
import NFC_KmxFrames
import NFE_NFC_LaterGeometry
import NFE_NFC_LaterJoin
import NFE_NFC_LaterSource
import NFE_NFC_MainPacket
import NFC_OpeningFrame
import NFE_NFC_PacketDomains
import NFE_NFC_PushCut
import NFE_NFC_RawAssociation
import NFE_NFC_RawValues
import NFE_NFC_ReceiverModel
import NFC_ScalarAdd
import NFE_NFC_StepAssociation
import NFE_NFC_TailAssociation
import NFE_NFC_TailPacket
import NFE_NFC_TailState
import NFE_NFC_TailTrace
import NFC_WideCanonical
import NFE_NFC_WrapperPacket

#print axioms AspisR1.NFC_AddDomain.cm
#print axioms AspisR1.NFC_AddDomain.qm
#print axioms AspisR1.NFC_AddDomain.total
#print axioms AspisR1.NFC_AddDomain.canonical
#print axioms AspisR1.NFC_ArrayFour.shape
#print axioms NFE_NFC_CalleeDomains.private_canon
#print axioms NFE_NFC_CalleeDomains.from_wide
#print axioms NFE_NFC_CalleeDomains.from_limbs
#print axioms NFE_NFC_CalleeDomains.checked
#print axioms NFE_NFC_CalleeDomains.value
#print axioms NFE_NFC_CalleeDomains.scalar
#print axioms NFE_NFC_CalleeDomains.total
#print axioms AspisR1.NFE_NFC_ChainAssociation.actual
#print axioms AspisR1.NFE_NFC_ChainAssociation.finish
#print axioms AspisR1.NFE_NFC_ChainAssociation.zero
#print axioms AspisR1.NFC_CheckedArithmetic.add
#print axioms AspisR1.NFC_CheckedArithmetic.mul
#print axioms AspisR1.NFE_NFC_DotDomain.accepted
#print axioms AspisR1.NFE_NFC_DotPushCut.source
#print axioms AspisR1.NFE_NFC_DotPushFour.source
#print axioms AspisR1.NFE_NFC_DotPushStep.source
#print axioms AspisR1.NFE_NFC_DotPushTotal.source
#print axioms AspisR1.NFE_NFC_DotWordStep.fold_bound
#print axioms AspisR1.NFE_NFC_DotWordStep.value
#print axioms AspisR1.NFE_NFC_DotWordStep.reduced
#print axioms AspisR1.NFE_NFC_FinalCalls.finish
#print axioms AspisR1.NFE_NFC_FinalCalls.add
#print axioms AspisR1.NFE_NFC_FirstGeometry.accepted
#print axioms AspisR1.NFE_NFC_FirstJoin.association
#print axioms AspisR1.NFE_NFC_FirstSource.cut
#print axioms AspisR1.NFE_NFC_FirstSource.domains
#print axioms AspisR1.NFE_NFC_FourDomain.accepted
#print axioms AspisR1.NFE_NFC_HeadDomain.canonical
#print axioms NFC_KmxFrames.final_region
#print axioms NFC_KmxFrames.frame
#print axioms NFC_KmxFrames.source_window
#print axioms NFC_KmxFrames.output_frame
#print axioms AspisR1.NFE_NFC_LaterGeometry.accepted
#print axioms AspisR1.NFE_NFC_LaterJoin.association
#print axioms AspisR1.NFE_NFC_LaterSource.cut
#print axioms AspisR1.NFE_NFC_LaterSource.domains
#print axioms AspisR1.NFE_NFC_MainPacket.of_run
#print axioms AspisR1.NFE_NFC_MainPacket.replay
#print axioms AspisR1.NFE_NFC_MainPacket.domains
#print axioms NFC_OpeningFrame.geometry
#print axioms NFC_OpeningFrame.frame
#print axioms AspisR1.NFE_NFC_PacketDomains.counts
#print axioms AspisR1.NFE_NFC_PacketDomains.inputs
#print axioms AspisR1.NFE_NFC_PacketDomains.finish
#print axioms AspisR1.NFE_NFC_PacketDomains.native_counts
#print axioms AspisR1.NFE_NFC_PushCut.actual
#print axioms AspisR1.NFE_NFC_PushCut.count
#print axioms AspisR1.NFE_NFC_RawAssociation.source_eq
#print axioms AspisR1.NFE_NFC_RawValues.source
#print axioms AspisR1.NFE_NFC_ReceiverModel.roundtrip
#print axioms AspisR1.NFE_NFC_ReceiverModel.represents
#print axioms AspisR1.NFC_ScalarAdd.total
#print axioms AspisR1.NFE_NFC_StepAssociation.exact
#print axioms AspisR1.NFE_NFC_StepAssociation.packet
#print axioms AspisR1.NFE_NFC_TailAssociation.source
#print axioms AspisR1.NFE_NFC_TailPacket.of_run
#print axioms AspisR1.NFE_NFC_TailPacket.replay
#print axioms AspisR1.NFE_NFC_TailState.new_count
#print axioms AspisR1.NFE_NFC_TailState.finish_canonical
#print axioms AspisR1.NFE_NFC_TailState.chain
#print axioms AspisR1.NFE_NFC_TailState.accepted
#print axioms AspisR1.NFE_NFC_TailTrace.unwrap_unit
#print axioms AspisR1.NFE_NFC_TailTrace.accepted
#print axioms AspisR1.NFC_WideCanonical.from_limbs
#print axioms AspisR1.NFE_NFC_WrapperPacket.accepted
