import RPx_Deployed
import NFC_AddDomain
import NFC_ArrayFour
import NFC_CalleeDomains
import NFC_ChainAssociation
import NFC_CheckedArithmetic
import NFC_DotDomain
import NFC_DotPushCut
import NFC_DotPushFour
import NFC_DotPushStep
import NFC_DotPushTotal
import NFC_DotWordStep
import NFC_FinalCalls
import NFC_FirstGeometry
import NFC_FirstJoin
import NFC_FirstSource
import NFC_FourDomain
import NFC_HeadDomain
import NFC_KmxFrames
import NFC_LaterGeometry
import NFC_LaterJoin
import NFC_LaterSource
import NFC_MainPacket
import NFC_OpeningFrame
import NFC_PacketDomains
import NFC_PushCut
import NFC_RawAssociation
import NFC_RawValues
import NFC_ReceiverModel
import NFC_ScalarAdd
import NFC_StepAssociation
import NFC_TailAssociation
import NFC_TailPacket
import NFC_TailState
import NFC_TailTrace
import NFC_WideCanonical
import NFC_WrapperPacket

#print axioms AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NFC_AddDomain.cm
#print axioms AspisR1.NFC_AddDomain.qm
#print axioms AspisR1.NFC_AddDomain.total
#print axioms AspisR1.NFC_AddDomain.canonical
#print axioms AspisR1.NFC_ArrayFour.shape
#print axioms NFC_CalleeDomains.private_canon
#print axioms NFC_CalleeDomains.from_wide
#print axioms NFC_CalleeDomains.from_limbs
#print axioms NFC_CalleeDomains.checked
#print axioms NFC_CalleeDomains.value
#print axioms NFC_CalleeDomains.scalar
#print axioms NFC_CalleeDomains.total
#print axioms AspisR1.NFC_ChainAssociation.actual
#print axioms AspisR1.NFC_ChainAssociation.finish
#print axioms AspisR1.NFC_ChainAssociation.zero
#print axioms AspisR1.NFC_CheckedArithmetic.add
#print axioms AspisR1.NFC_CheckedArithmetic.mul
#print axioms AspisR1.NFC_DotDomain.accepted
#print axioms AspisR1.NFC_DotPushCut.source
#print axioms AspisR1.NFC_DotPushFour.source
#print axioms AspisR1.NFC_DotPushStep.source
#print axioms AspisR1.NFC_DotPushTotal.source
#print axioms AspisR1.NFC_DotWordStep.fold_bound
#print axioms AspisR1.NFC_DotWordStep.value
#print axioms AspisR1.NFC_DotWordStep.reduced
#print axioms AspisR1.NFC_FinalCalls.finish
#print axioms AspisR1.NFC_FinalCalls.add
#print axioms AspisR1.NFC_FirstGeometry.accepted
#print axioms AspisR1.NFC_FirstJoin.association
#print axioms AspisR1.NFC_FirstSource.cut
#print axioms AspisR1.NFC_FirstSource.domains
#print axioms AspisR1.NFC_FourDomain.accepted
#print axioms AspisR1.NFC_HeadDomain.canonical
#print axioms NFC_KmxFrames.final_region
#print axioms NFC_KmxFrames.frame
#print axioms NFC_KmxFrames.source_window
#print axioms NFC_KmxFrames.output_frame
#print axioms AspisR1.NFC_LaterGeometry.accepted
#print axioms AspisR1.NFC_LaterJoin.association
#print axioms AspisR1.NFC_LaterSource.cut
#print axioms AspisR1.NFC_LaterSource.domains
#print axioms AspisR1.NFC_MainPacket.of_run
#print axioms AspisR1.NFC_MainPacket.replay
#print axioms AspisR1.NFC_MainPacket.domains
#print axioms NFC_OpeningFrame.geometry
#print axioms NFC_OpeningFrame.frame
#print axioms AspisR1.NFC_PacketDomains.counts
#print axioms AspisR1.NFC_PacketDomains.inputs
#print axioms AspisR1.NFC_PacketDomains.finish
#print axioms AspisR1.NFC_PacketDomains.native_counts
#print axioms AspisR1.NFC_PushCut.actual
#print axioms AspisR1.NFC_PushCut.count
#print axioms AspisR1.NFC_RawAssociation.source_eq
#print axioms AspisR1.NFC_RawValues.source
#print axioms AspisR1.NFC_ReceiverModel.roundtrip
#print axioms AspisR1.NFC_ReceiverModel.represents
#print axioms AspisR1.NFC_ScalarAdd.total
#print axioms AspisR1.NFC_StepAssociation.exact
#print axioms AspisR1.NFC_StepAssociation.packet
#print axioms AspisR1.NFC_TailAssociation.source
#print axioms AspisR1.NFC_TailPacket.of_run
#print axioms AspisR1.NFC_TailPacket.replay
#print axioms AspisR1.NFC_TailState.new_count
#print axioms AspisR1.NFC_TailState.finish_canonical
#print axioms AspisR1.NFC_TailState.chain
#print axioms AspisR1.NFC_TailState.accepted
#print axioms AspisR1.NFC_TailTrace.unwrap_unit
#print axioms AspisR1.NFC_TailTrace.accepted
#print axioms AspisR1.NFC_WideCanonical.from_limbs
#print axioms AspisR1.NFC_WrapperPacket.accepted
