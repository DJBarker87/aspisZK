import Lean
import OraclePortSelectedDraft
import OraclePortBatchDraft
import OraclePortFrozenOrderSlot
import OraclePortStoredExperimentC4
import OraclePortCoverageDraft
import OraclePortSparseLeafCountC3
import OraclePortRepresentativeCountC3
import OraclePortSixSlotBudgetC3
import OraclePortStoredParserC4
import OraclePortStoredAdmissionC4
import OraclePortDataChoiceDraft
import OraclePortReaderSourceDraft
import OraclePortStoredChecksC4
import OraclePortStoredDecisionDraftC4
import OraclePortCandidateChecksC4
import OraclePortSelectedArithmeticC4
import OraclePortSelectedObservationsC6
import OraclePortSemanticObservationsC6
import OraclePortReaderPlumbingC6
import OraclePortOpeningRewordC6
import OraclePortSemanticProjectionC6
import OraclePortMatchingRewordC6
import OraclePortSelectedConsumerC6
import OraclePortObservationTransportC6
import OraclePortPackedChoiceC4
import OraclePortMapObservationsC6
import OraclePortCandidateWordsC6
import OraclePortRouteIndexC4
import OraclePortDuplicateBindingDraft
import OraclePortStoredLeafRecoveryC4
import OraclePortIndexedRecoveryC4
import OraclePortStoredWidthsC4
import OraclePortAllSelectedRecoveryC6
import OraclePortRecoveredAcceptanceC6
import OraclePortStoredAccountingC4
import OraclePortStoredProjectionC4
import OraclePortReachedRunC6
import OraclePortFrameShapesC6
import OraclePortParsedRootsC6
import OraclePortRootBytesC6
import OraclePortReachedRootsC6
import OraclePortActualAcceptanceC6
import OraclePortRowsCanonicalC6
import OraclePortCanonicalAcceptanceC6
import OraclePortSamplerPrefixDraft
import OraclePortCompletionDraft
import OraclePortStoredAcceptanceC6
import OraclePortStoredReductionC7
import OraclePortStoredConsumerC7
import OraclePortPureOutputC7
import R9PoolConcreteExperiment
import OraclePortPool
import OracleDecisionPrereqNumeric
import OracleDecisionMultiNumeric
import OraclePortHeadline
import OraclePortStoredProbabilityC7
import OraclePortRuntimeBindingC7
import OraclePortJoinSplitCore
import OraclePortJoinSplitOrdering
import OraclePortShortCircuitCore
import OraclePortJoinSplitDecision
import OraclePortShortCircuitDecision
import OraclePortFrozenOrderDecision
import OraclePortFrozenOrderAccepted
import OraclePortCkptAbi2Reached
import OraclePortCkptAbi3Canonical
import OraclePortCkptAbi4Decode
import OraclePortCkptAbi5Codec
import CheckpointP6EncodeK
import MultiproofParserRef.Types
import MultiproofParserRef.Funs
import MultiproofConeWordScan
import R1ExtractedM31Parser
import AspisR72Sampler.Types
import AspisR72Sampler.Funs
import AspisV8R19.SamplerWordRead
import AspisV8R19.SqueezeSourceExecution
import AspisV8R19.SqueezeOracleBridge
import AspisV8R19.SamplerWordBridge
import AeneasWordCodec
import R1M31ParserRefinement
import R1M31ParserCanonicality
import R1M31ParserArray
import MultiproofConeEndian
import MultiproofConeCanonical
import CheckpointP6KBytes
import CheckpointBytesArithmetic
import CheckpointBytesE
import CheckpointBytesEC5
import CheckpointBytesBlocks
import CheckpointBytesLookup
import CheckpointBytesBodyArithmetic
import CheckpointBytesHeader
import CheckpointBytesDigest
import CheckpointBytesSparseDigest
import CheckpointBytesSparseE
import CheckpointBytesK
import CheckpointBytesSparseK
import CheckpointBytesETotal
import CheckpointBytesWord

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `OraclePortSelectedDraft, `OraclePortBatchDraft, `OraclePortFrozenOrderSlot, `OraclePortStoredExperimentC4, `OraclePortCoverageDraft, `OraclePortSparseLeafCountC3, `OraclePortRepresentativeCountC3, `OraclePortSixSlotBudgetC3, `OraclePortStoredParserC4, `OraclePortStoredAdmissionC4, `OraclePortDataChoiceDraft, `OraclePortReaderSourceDraft, `OraclePortStoredChecksC4, `OraclePortStoredDecisionDraftC4, `OraclePortCandidateChecksC4, `OraclePortSelectedArithmeticC4, `OraclePortSelectedObservationsC6, `OraclePortSemanticObservationsC6, `OraclePortReaderPlumbingC6, `OraclePortOpeningRewordC6, `OraclePortSemanticProjectionC6, `OraclePortMatchingRewordC6, `OraclePortSelectedConsumerC6, `OraclePortObservationTransportC6, `OraclePortPackedChoiceC4, `OraclePortMapObservationsC6, `OraclePortCandidateWordsC6, `OraclePortRouteIndexC4, `OraclePortDuplicateBindingDraft, `OraclePortStoredLeafRecoveryC4, `OraclePortIndexedRecoveryC4, `OraclePortStoredWidthsC4, `OraclePortAllSelectedRecoveryC6, `OraclePortRecoveredAcceptanceC6, `OraclePortStoredAccountingC4, `OraclePortStoredProjectionC4, `OraclePortReachedRunC6, `OraclePortFrameShapesC6, `OraclePortParsedRootsC6, `OraclePortRootBytesC6, `OraclePortReachedRootsC6, `OraclePortActualAcceptanceC6, `OraclePortRowsCanonicalC6, `OraclePortCanonicalAcceptanceC6, `OraclePortSamplerPrefixDraft, `OraclePortCompletionDraft, `OraclePortStoredAcceptanceC6, `OraclePortStoredReductionC7, `OraclePortStoredConsumerC7, `OraclePortPureOutputC7, `R9PoolConcreteExperiment, `OraclePortPool, `OracleDecisionPrereqNumeric, `OracleDecisionMultiNumeric, `OraclePortHeadline, `OraclePortStoredProbabilityC7, `OraclePortRuntimeBindingC7, `OraclePortJoinSplitCore, `OraclePortJoinSplitOrdering, `OraclePortShortCircuitCore, `OraclePortJoinSplitDecision, `OraclePortShortCircuitDecision, `OraclePortFrozenOrderDecision, `OraclePortFrozenOrderAccepted, `OraclePortCkptAbi2Reached, `OraclePortCkptAbi3Canonical, `OraclePortCkptAbi4Decode, `OraclePortCkptAbi5Codec, `CheckpointP6EncodeK, `MultiproofParserRef.Types, `MultiproofParserRef.Funs, `MultiproofConeWordScan, `R1ExtractedM31Parser, `AspisR72Sampler.Types, `AspisR72Sampler.Funs, `AspisV8R19.SamplerWordRead, `AspisV8R19.SqueezeSourceExecution, `AspisV8R19.SqueezeOracleBridge, `AspisV8R19.SamplerWordBridge, `AeneasWordCodec, `R1M31ParserRefinement, `R1M31ParserCanonicality, `R1M31ParserArray, `MultiproofConeEndian, `MultiproofConeCanonical, `CheckpointP6KBytes, `CheckpointBytesArithmetic, `CheckpointBytesE, `CheckpointBytesEC5, `CheckpointBytesBlocks, `CheckpointBytesLookup, `CheckpointBytesBodyArithmetic, `CheckpointBytesHeader, `CheckpointBytesDigest, `CheckpointBytesSparseDigest, `CheckpointBytesSparseE, `CheckpointBytesK, `CheckpointBytesSparseK, `CheckpointBytesETotal, `CheckpointBytesWord ]
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
