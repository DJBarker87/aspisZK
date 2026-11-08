-- Focused Run 5b plus NNV check only; no A1 term or G0 claim.
import NNH_Run5bCombined
import NNV_AfterstatePort
import NNV_CheckpointDigest
import NNV_CheckpointValue
import NNV_CommonAssociation
import NNV_CurrentGeometry
import NNV_CurrentScan
import NNV_DecodeP1880
import NNV_GeometryBody
import NNV_GeometryBranches
import NNV_GeometryCallbacks
import NNV_GeometryEq
import NNV_GeometryIndexPorts
import NNV_GeometryInstallSlots
import NNV_GeometryOuter
import NNV_GeometryPrefix
import NNV_GeometryPrefixSelected
import NNV_GeometryQuery
import NNV_GeometryQueryForm
import NNV_GeometrySelectedStd
import NNV_GeometryTerminal
import NNV_ObservedCut
import NNV_PreparedAtHost
import NNV_PreparedDomainPorts
import NNV_PreparedInputs
import NNV_PreparedNative
import NNV_PreparedPorts
import NNV_PreparedReturned
import NNV_PreparedStateTransport
import NNV_ScanWeakErr
import NNV_SemanticBegin
import NNV_SemanticParse
import NNV_SemanticPrefix
import NNV_SemanticTranscript
import NNV_WeakErrHost

#print axioms AspisR1.NNV_AfterstatePort.source
#print axioms AspisR1.NNV_CheckpointDigest.source
#print axioms AspisR1.NNV_CheckpointValue.source
#print axioms AspisR1.NNV_CommonAssociation.afterstate
#print axioms AspisR1.NNV_CommonAssociation.common
#print axioms AspisR1.NNV_CurrentGeometry.returned
#print axioms AspisR1.NNV_CurrentGeometry.slot
#print axioms AspisR1.NNV_CurrentGeometry.source
#print axioms AspisR1.NNV_CurrentScan.returned
#print axioms AspisR1.NNV_CurrentScan.slot
#print axioms AspisR1.NNV_CurrentScan.source
#print axioms AspisR1.NNV_DecodeP1880.native
#print axioms AspisR1.NNV_DecodeP1880.returned
#print axioms AspisR1.NNV_GeometryBody.source
#print axioms AspisR1.NNV_GeometryBranches.body
#print axioms AspisR1.NNV_GeometryCallbacks.gather_inner
#print axioms AspisR1.NNV_GeometryCallbacks.gather_outer
#print axioms AspisR1.NNV_GeometryCallbacks.zero_test
#print axioms AspisR1.NNV_GeometryEq.installed
#print axioms AspisR1.NNV_GeometryEq.source
#print axioms AspisR1.NNV_GeometryIndexPorts.first
#print axioms AspisR1.NNV_GeometryIndexPorts.second
#print axioms AspisR1.NNV_GeometryIndexPorts.third
#print axioms AspisR1.NNV_GeometryInstallSlots.any
#print axioms AspisR1.NNV_GeometryInstallSlots.array
#print axioms AspisR1.NNV_GeometryInstallSlots.empty
#print axioms AspisR1.NNV_GeometryInstallSlots.iterator
#print axioms AspisR1.NNV_GeometryInstallSlots.mapped
#print axioms AspisR1.NNV_GeometryInstallSlots.zero
#print axioms AspisR1.NNV_GeometryOuter.loop
#print axioms AspisR1.NNV_GeometryOuter.source
#print axioms AspisR1.NNV_GeometryOuter.stage
#print axioms AspisR1.NNV_GeometryPrefix.source
#print axioms AspisR1.NNV_GeometryPrefixSelected.source
#print axioms AspisR1.NNV_GeometryQuery.fibre
#print axioms AspisR1.NNV_GeometryQuery.source
#print axioms AspisR1.NNV_GeometryQueryForm.source
#print axioms AspisR1.NNV_GeometrySelectedStd.any
#print axioms AspisR1.NNV_GeometrySelectedStd.array
#print axioms AspisR1.NNV_GeometrySelectedStd.empty
#print axioms AspisR1.NNV_GeometrySelectedStd.iterator
#print axioms AspisR1.NNV_GeometrySelectedStd.mapped
#print axioms AspisR1.NNV_GeometrySelectedStd.zero
#print axioms AspisR1.NNV_GeometryTerminal.source
#print axioms AspisR1.NNV_ObservedCut.returned
#print axioms AspisR1.NNV_PreparedAtHost.source
#print axioms AspisR1.NNV_PreparedDomainPorts.domain
#print axioms AspisR1.NNV_PreparedDomainPorts.input
#print axioms AspisR1.NNV_PreparedInputs.field
#print axioms AspisR1.NNV_PreparedInputs.scratch_input
#print axioms AspisR1.NNV_PreparedInputs.semantic
#print axioms AspisR1.NNV_PreparedInputs.view_input
#print axioms AspisR1.NNV_PreparedNative.returned
#print axioms AspisR1.NNV_PreparedPorts.source
#print axioms AspisR1.NNV_PreparedReturned.model
#print axioms AspisR1.NNV_PreparedStateTransport.field
#print axioms AspisR1.NNV_PreparedStateTransport.prepared
#print axioms AspisR1.NNV_PreparedStateTransport.scratch
#print axioms AspisR1.NNV_ScanWeakErr.accepted
#print axioms AspisR1.NNV_ScanWeakErr.rejected
#print axioms AspisR1.NNV_SemanticBegin.returned
#print axioms AspisR1.NNV_SemanticParse.association
#print axioms AspisR1.NNV_SemanticParse.returned
#print axioms AspisR1.NNV_SemanticPrefix.returned
#print axioms AspisR1.NNV_SemanticTranscript.returned
#print axioms AspisR1.NNV_SemanticTranscript.source
#print axioms AspisR1.NNV_WeakErrHost.modelRet1
