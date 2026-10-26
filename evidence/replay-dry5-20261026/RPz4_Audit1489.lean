import Lean
import R1CandidateFieldParsers
import S8OwnedP6FieldParserTransport
import S8OwnedP6QMParserTransport
import R1CandidateParserSupport
import R1ParserArraySlice
import R1CandidateCM31Parser
import R1CandidateQM31Parser
import R1CandidateParserByteOrder
import R1CandidateStrictQM31Parser
import S8OwnedP6StrictParser
import S8OwnedP6Scan
import S8OwnedP6StrictScanModel
import S7OwnedP6RowContract
import S8OwnedP6Residue
import S8OwnedP6Certificate
import S8Kani2FinishCertificate
import S8Kani2FinishReferenceJoin
import S8Kani2CallerJoin
import S7Kani3CallerStep
import S7Kani3CallerTrace
import S7JoinRowsTrace
import S7JoinQueryRows
import S8JoinCompactChunks
import S8JoinCompactTotal
import S8JoinFrozenScan
import S2LeadInterface
import S2W_LeadInterface
import AdapterRwTypes
import AdapterRwModel
import S2Z_Oracle
import S2W_OracleAudit
import S2W_SuccessOracle
import S2TrustedSdkBorrow
import S2W_TrustedStd
import AdapterRwRuntimeAdmission
import AdapterRwSdkSnapshots
import S2W_WrapperLaws
import AdapterRwCuts
import AdapterRwScalar
import AdapterRwConstants
import AdapterRwRanges
import AdapterRwAccepted
import AdapterRwLeadInputs
import S2X_SnapshotWrite
import ExtractedAdapterWithdrawalBindings
import R20PoolStatementAgreement
import R9PoolRuntimeBinding
import S2X_RuntimeRetention
import S2W_EntryWriteHistory
import MultiproofConeByteEquality
import MultiproofConeBool
import MultiproofConeFrameHeader
import MultiproofConeHeaderControl
import MultiproofConeCodec
import MultiproofConeRowShape
import MultiproofConeRowEncoding
import MultiproofConeFrameModel
import MultiproofConeQMScan
import MultiproofConeRead16
import MultiproofConeCanonicalAppend
import MultiproofConeCompactScan
import MultiproofConeVecLaws
import MultiproofConeExpandModel
import MultiproofConeExpansion
import MultiproofConeExpansionLength
import MultiproofConeLogicalPayload
import MultiproofConeSemanticModel
import MultiproofConePayloadControl
import MultiproofConeRowStep
import MultiproofConeRowScalars
import MultiproofConeHeader
import MultiproofConeOpeningScan
import MultiproofConeOpeningRows
import MultiproofConeSliceComposition
import MultiproofConeStrictScan
import MultiproofConeParserControl
import MultiproofConePush
import MultiproofConeFrameBuild
import MultiproofConeSemanticRows
import MultiproofConeParserTotal
import S2Y_ChildGeometry
import S2Y_OwnedChildren
import S2Y_ForestPublic
import S2W_ChildJoins
import S2W_Trace
import S2W_Outer
import S2W_OuterErasure
import S2W_TraceFacts
import S2W_Observation
import S2W_FinalAudit
import S2X_SecondCut
import S2W_ExtractionBoundary
import S2W_AuthenticatedInputs
import S2W_NativeConsolidation
import AspisR1PublicPreparation.Types
import AspisR1PublicPreparation.Funs
import ExtractedDigest32Transcript
import ExtractedDigest32Callers
import AspisR1Qm31SamplerIndex.Types
import AspisR1Qm31SamplerIndex.Funs

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1CandidateFieldParsers, `S8OwnedP6FieldParserTransport, `S8OwnedP6QMParserTransport, `R1CandidateParserSupport, `R1ParserArraySlice, `R1CandidateCM31Parser, `R1CandidateQM31Parser, `R1CandidateParserByteOrder, `R1CandidateStrictQM31Parser, `S8OwnedP6StrictParser, `S8OwnedP6Scan, `S8OwnedP6StrictScanModel, `S7OwnedP6RowContract, `S8OwnedP6Residue, `S8OwnedP6Certificate, `S8Kani2FinishCertificate, `S8Kani2FinishReferenceJoin, `S8Kani2CallerJoin, `S7Kani3CallerStep, `S7Kani3CallerTrace, `S7JoinRowsTrace, `S7JoinQueryRows, `S8JoinCompactChunks, `S8JoinCompactTotal, `S8JoinFrozenScan, `S2LeadInterface, `S2W_LeadInterface, `AdapterRwTypes, `AdapterRwModel, `S2Z_Oracle, `S2W_OracleAudit, `S2W_SuccessOracle, `S2TrustedSdkBorrow, `S2W_TrustedStd, `AdapterRwRuntimeAdmission, `AdapterRwSdkSnapshots, `S2W_WrapperLaws, `AdapterRwCuts, `AdapterRwScalar, `AdapterRwConstants, `AdapterRwRanges, `AdapterRwAccepted, `AdapterRwLeadInputs, `S2X_SnapshotWrite, `ExtractedAdapterWithdrawalBindings, `R20PoolStatementAgreement, `R9PoolRuntimeBinding, `S2X_RuntimeRetention, `S2W_EntryWriteHistory, `MultiproofConeByteEquality, `MultiproofConeBool, `MultiproofConeFrameHeader, `MultiproofConeHeaderControl, `MultiproofConeCodec, `MultiproofConeRowShape, `MultiproofConeRowEncoding, `MultiproofConeFrameModel, `MultiproofConeQMScan, `MultiproofConeRead16, `MultiproofConeCanonicalAppend, `MultiproofConeCompactScan, `MultiproofConeVecLaws, `MultiproofConeExpandModel, `MultiproofConeExpansion, `MultiproofConeExpansionLength, `MultiproofConeLogicalPayload, `MultiproofConeSemanticModel, `MultiproofConePayloadControl, `MultiproofConeRowStep, `MultiproofConeRowScalars, `MultiproofConeHeader, `MultiproofConeOpeningScan, `MultiproofConeOpeningRows, `MultiproofConeSliceComposition, `MultiproofConeStrictScan, `MultiproofConeParserControl, `MultiproofConePush, `MultiproofConeFrameBuild, `MultiproofConeSemanticRows, `MultiproofConeParserTotal, `S2Y_ChildGeometry, `S2Y_OwnedChildren, `S2Y_ForestPublic, `S2W_ChildJoins, `S2W_Trace, `S2W_Outer, `S2W_OuterErasure, `S2W_TraceFacts, `S2W_Observation, `S2W_FinalAudit, `S2X_SecondCut, `S2W_ExtractionBoundary, `S2W_AuthenticatedInputs, `S2W_NativeConsolidation, `AspisR1PublicPreparation.Types, `AspisR1PublicPreparation.Funs, `ExtractedDigest32Transcript, `ExtractedDigest32Callers, `AspisR1Qm31SamplerIndex.Types, `AspisR1Qm31SamplerIndex.Funs ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ4_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ4_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ4_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ4_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ4_AUDIT_COMPLETE declarations={count} modules={selected.size}"
