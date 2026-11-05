import NGK_COMBINED_IMPORT
import NID_COMBINED_IMPORT
import NIL_COMBINED_IMPORT
import NIY_FirstRawCut
import NIY_FirstECut
import NIY_RawTransport
import NIY_AfterKappa
import NIY_CohortRawCut
import NIY_AfterAlpha0
import NIY_AfterAlpha1
import NIY_AfterRho
import NIY_QueryRead
import NIY_QueryCut
import NIY_ValidationCut
import NIY_SemanticCut
import NIY_AfterZ0x
import NIY_AfterZ0y
import NIY_AfterZ1x
import NIY_AfterZ1y
import NIY_AfterClaim
import NIY_AfterRhs
import NIY_AfterPower
import NIY_AllocationCut
import NIY_FinalCut
import NIY_C_FirstECut
import NIY_C_AfterKappa
import NIY_C_AfterAlpha0
import NIY_C_AfterAlpha1
import NIY_C_AfterRho
import NIY_C_QueryCut
import NIY_C_ValidationCut
import NIY_C_SemanticCut
import NIY_C_AfterZ0x
import NIY_C_AfterZ0y
import NIY_C_AfterZ1x
import NIY_C_AfterZ1y
import NIY_C_AfterClaim
import NIY_C_AfterRhs
import NIY_C_AfterPower
import NIY_C_AllocationCut
import NIY_C_FinalCut
import NIY_FinalPort
import NIY_SectionBind
import NIY_WeightsPort
import NIY_AllocationPort
import NIY_PowerReadPort
import NIY_RhsReadPort
import NIY_ClaimReadPort
import NIY_Z1yReadPort
import NIY_Z1xReadPort
import NIY_Z0yReadPort
import NIY_Z0xReadPort
import NIY_SemanticPort
import NIY_ValidationPort
import NIY_QueryTransport
import NIY_QueryPort
import NIY_RhoReadPort
import NIY_Alpha1ReadPort
import NIY_Alpha0ReadPort
import NIY_KappaReadPort
import NIY_GammaReadPort
import NIY_TailPort
import NIY_ResumePort
import NIY_WeightFrame
import NIY_NativeFinalCuts
import NIY_ScanCuts
import NIY_ResumeFields
import NIY_ReaderFrames
import NIY_EarlyDomains
import NIY_NativeCuts

#check NIY_FirstRawCut.fresh_source
#print axioms NIY_FirstRawCut.fresh_source
#check NIY_FirstECut.source
#print axioms NIY_FirstECut.source
#check NIY_RawTransport.raw
#print axioms NIY_RawTransport.raw
#check NIY_RawTransport.first3
#print axioms NIY_RawTransport.first3
#check NIY_AfterKappa.source
#print axioms NIY_AfterKappa.source
#check NIY_CohortRawCut.source
#print axioms NIY_CohortRawCut.source
#check NIY_AfterAlpha0.source
#print axioms NIY_AfterAlpha0.source
#check NIY_AfterAlpha1.source
#print axioms NIY_AfterAlpha1.source
#check NIY_AfterRho.source
#print axioms NIY_AfterRho.source
#check NIY_QueryRead.assoc
#print axioms NIY_QueryRead.assoc
#check NIY_QueryRead.prod_bind
#print axioms NIY_QueryRead.prod_bind
#check NIY_QueryRead.ok_bind
#print axioms NIY_QueryRead.ok_bind
#check NIY_QueryRead.continuation
#print axioms NIY_QueryRead.continuation
#check NIY_QueryCut.source
#print axioms NIY_QueryCut.source
#check NIY_ValidationCut.source
#print axioms NIY_ValidationCut.source
#check NIY_SemanticCut.source
#print axioms NIY_SemanticCut.source
#check NIY_AfterZ0x.source
#print axioms NIY_AfterZ0x.source
#check NIY_AfterZ0y.source
#print axioms NIY_AfterZ0y.source
#check NIY_AfterZ1x.source
#print axioms NIY_AfterZ1x.source
#check NIY_AfterZ1y.source
#print axioms NIY_AfterZ1y.source
#check NIY_AfterClaim.source
#print axioms NIY_AfterClaim.source
#check NIY_AfterRhs.source
#print axioms NIY_AfterRhs.source
#check NIY_AfterPower.source
#print axioms NIY_AfterPower.source
#check NIY_AllocationCut.source
#print axioms NIY_AllocationCut.source
#check NIY_FinalCut.source
#print axioms NIY_FinalCut.source
#check NIY_C_FirstECut.source
#print axioms NIY_C_FirstECut.source
#check NIY_C_AfterKappa.source
#print axioms NIY_C_AfterKappa.source
#check NIY_C_AfterAlpha0.source
#print axioms NIY_C_AfterAlpha0.source
#check NIY_C_AfterAlpha1.source
#print axioms NIY_C_AfterAlpha1.source
#check NIY_C_AfterRho.source
#print axioms NIY_C_AfterRho.source
#check NIY_C_QueryCut.source
#print axioms NIY_C_QueryCut.source
#check NIY_C_ValidationCut.source
#print axioms NIY_C_ValidationCut.source
#check NIY_C_SemanticCut.source
#print axioms NIY_C_SemanticCut.source
#check NIY_C_AfterZ0x.source
#print axioms NIY_C_AfterZ0x.source
#check NIY_C_AfterZ0y.source
#print axioms NIY_C_AfterZ0y.source
#check NIY_C_AfterZ1x.source
#print axioms NIY_C_AfterZ1x.source
#check NIY_C_AfterZ1y.source
#print axioms NIY_C_AfterZ1y.source
#check NIY_C_AfterClaim.source
#print axioms NIY_C_AfterClaim.source
#check NIY_C_AfterRhs.source
#print axioms NIY_C_AfterRhs.source
#check NIY_C_AfterPower.source
#print axioms NIY_C_AfterPower.source
#check NIY_C_AllocationCut.source
#print axioms NIY_C_AllocationCut.source
#check NIY_C_FinalCut.source
#print axioms NIY_C_FinalCut.source
#check NIY_FinalPort.source
#print axioms NIY_FinalPort.source
#check NIY_SectionBind.sectionReply
#print axioms NIY_SectionBind.sectionReply
#check NIY_SectionBind.reverse_port
#print axioms NIY_SectionBind.reverse_port
#check NIY_SectionBind.forwardReply
#print axioms NIY_SectionBind.forwardReply
#check NIY_WeightsPort.source
#print axioms NIY_WeightsPort.source
#check NIY_AllocationPort.source
#print axioms NIY_AllocationPort.source
#check NIY_PowerReadPort.source
#print axioms NIY_PowerReadPort.source
#check NIY_RhsReadPort.source
#print axioms NIY_RhsReadPort.source
#check NIY_ClaimReadPort.source
#print axioms NIY_ClaimReadPort.source
#check NIY_Z1yReadPort.source
#print axioms NIY_Z1yReadPort.source
#check NIY_Z1xReadPort.source
#print axioms NIY_Z1xReadPort.source
#check NIY_Z0yReadPort.source
#print axioms NIY_Z0yReadPort.source
#check NIY_Z0xReadPort.source
#print axioms NIY_Z0xReadPort.source
#check NIY_SemanticPort.source
#print axioms NIY_SemanticPort.source
#check NIY_ValidationPort.source
#print axioms NIY_ValidationPort.source
#check NIY_QueryTransport.continuation
#print axioms NIY_QueryTransport.continuation
#check NIY_QueryPort.source
#print axioms NIY_QueryPort.source
#check NIY_RhoReadPort.source
#print axioms NIY_RhoReadPort.source
#check NIY_Alpha1ReadPort.source
#print axioms NIY_Alpha1ReadPort.source
#check NIY_Alpha0ReadPort.source
#print axioms NIY_Alpha0ReadPort.source
#check NIY_KappaReadPort.source
#print axioms NIY_KappaReadPort.source
#check NIY_GammaReadPort.source
#print axioms NIY_GammaReadPort.source
#check NIY_TailPort.source
#print axioms NIY_TailPort.source
#check NIY_ResumePort.source
#print axioms NIY_ResumePort.source
#check NIY_WeightFrame.scalar_ext
#print axioms NIY_WeightFrame.scalar_ext
#check NIY_WeightFrame.k_ext
#print axioms NIY_WeightFrame.k_ext
#check NIY_WeightFrame.payload
#print axioms NIY_WeightFrame.payload
#check NIY_WeightFrame.capacity_prefix
#print axioms NIY_WeightFrame.capacity_prefix
#check NIY_WeightFrame.capacity_to_final
#print axioms NIY_WeightFrame.capacity_to_final
#check NIY_ScanCuts.step_ok
#print axioms NIY_ScanCuts.step_ok
#check NIY_ScanCuts.prefix_ok
#print axioms NIY_ScanCuts.prefix_ok
#check NIY_ResumeFields.fields
#print axioms NIY_ResumeFields.fields
#check NIY_ResumeFields.reservation
#print axioms NIY_ResumeFields.reservation
#check NIY_ReaderFrames.raw
#print axioms NIY_ReaderFrames.raw
#check NIY_ReaderFrames.e
#print axioms NIY_ReaderFrames.e
#check NIY_EarlyDomains.first3
#print axioms NIY_EarlyDomains.first3
#check NIY_EarlyDomains.typed
#print axioms NIY_EarlyDomains.typed
#check NIY_NativeCuts.firstByte
#print axioms NIY_NativeCuts.firstByte
#check NIY_NativeCuts.firstCursor
#print axioms NIY_NativeCuts.firstCursor
#check NIY_NativeCuts.eReply
#print axioms NIY_NativeCuts.eReply
#check NIY_NativeCuts.kReply
#print axioms NIY_NativeCuts.kReply
#check NIY_NativeCuts.eValue
#print axioms NIY_NativeCuts.eValue
#check NIY_NativeCuts.kValue
#print axioms NIY_NativeCuts.kValue
#check NIY_NativeCuts.descriptor
#print axioms NIY_NativeCuts.descriptor
#check NIY_NativeCuts.eCursor
#print axioms NIY_NativeCuts.eCursor
#check NIY_NativeCuts.kCursor
#print axioms NIY_NativeCuts.kCursor
#check NIY_NativeFinalCuts.windowPre
#print axioms NIY_NativeFinalCuts.windowPre
#check NIY_NativeFinalCuts.windowCut
#print axioms NIY_NativeFinalCuts.windowCut
#check NIY_NativeFinalCuts.reserveCut
#print axioms NIY_NativeFinalCuts.reserveCut
#check NIY_NativeFinalCuts.weightPre
#print axioms NIY_NativeFinalCuts.weightPre
#check NIY_NativeFinalCuts.weightCut
#print axioms NIY_NativeFinalCuts.weightCut
#check NIY_ScanCuts.prefixCut
#print axioms NIY_ScanCuts.prefixCut
#check NIY_ScanCuts.m31Cut
#print axioms NIY_ScanCuts.m31Cut
#check NIY_ScanCuts.openingCut
#print axioms NIY_ScanCuts.openingCut
#check AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.RPx_Deployed.deployed
