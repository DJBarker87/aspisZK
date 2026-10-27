import Lean
import CurrentPreparedOrdinaryRankV1
import CurrentPreparedJointRankPrefix
import CurrentPreparedJointRankTrace
import CurrentPreparedJointRankMeaning
import PreparedSourcePowersJointRankV1
import PreparedSourcePowersEntryV1
import PreparedParsedInactiveV1
import SelectedWideViewInactiveV1
import SelectedWideViewPreparedEntryV1
import CurrentCompactInstalledPreparationV1
import CurrentOriginalPreparedNativeV1
import CurrentOriginalPreparedCarrierTransportV1
import CurrentOriginalPreparedInstallationV1
import S1BorrowedClaimPreparedBoundaryV1
import S1BorrowedClaimFirstCallerV1
import S2OwnedCurrentCarrierV1
import S2OwnedSourceInstallationV1
import S2SdkOwnedInstallationV1
import S2SdkOwnedReachabilityV1
import S2SdkOwnedDecodedReuseV1
import S2SdkOwnedGuardBodyV1
import S2SdkReadyAcquireV1
import S2SdkReadyStateV1
import S2SdkProofGateModelV1
import S2SdkProofPrefixTotalV1
import S2SdkProofGateTotalV1
import S2SdkGateAdmittedImageV1
import S2SdkProofComparatorV1
import S2SdkProofPrefixParentV1
import S2FrameOperationsTotalV1
import S2SdkBorrowedEquivalenceV1
import S2SdkProofGateJoinV1
import S2SdkAdmittedCallerV1
import S2SdkLinkedCallerV1
import S2SdkErrorBufferFrameV1
import S2SdkFixedInputCallerV1
import S2SdkCheckpointWriterV1
import S2SdkSavedFirstV1
import S2SdkFixedSavedFirstV1
import S126SdkFixedInputCurrentV1
import S126SdkFixedSavedCurrentV1
import S2SdkMetadataFrameV1
import S126SdkSavedAccountExportV1
import S2SdkCheckpointImageV1
import S2SdkFixedImageFirstV1
import S2SdkKeyEqualityV1
import S6CurrentVerifierCarrierV1
import S1M31EmbeddingTotalV1
import S1QueryTraceEmbeddingV1
import S1OriginalPreparedSourceEmbeddingV1
import S1OriginalSerializerInstallationV1
import S1OriginalSerializedRankTraceV1
import S1BorrowedClaimConcreteCallerV1
import S1SemanticVerifyReachabilityV1
import S1SemanticFinishRootsV1
import S1SemanticRootCopyV1
import S1PreparedSourceEffectsV1
import S1PreparedHashEffectsV1
import S1PreparedHashCodeV1
import S1PreparedOracleCodeV1
import S1PreparedOracleProgramLawsV1
import S1QueryReadPairProgramV1
import S1QueryByteChainV1
import S1QueryPairEvaluationV1
import S1QueryProgramRelationV1
import S1PreparedSilentCodeV1
import S1PreparedHashErasureV1
import S1PreparedScalarEffectsV1
import S1PreparedQueryEffectsV1
import S1PreparedCodeLawsV1
import S1QueryMaterializeEffectsV1
import S1PreparedCodeProductLawsV1
import S1QueryMaterializePairsV1
import S1QueryMaterializeProgramV1
import S1QueryMaterializeModelV1
import S1QueryModelContinuationV1
import S1QueryFinishProgramV1
import S1QueryFinishAcceptedV1
import S1QueryPackEightExactV1
import S1QueryWordModelV1
import S1QueryScanModelStepV1
import S1QueryScanDriverModelV1
import S1QueryAbsorbProgramV1
import S1QueryByteChainBudgetV1
import S1QueryRow31ProgramV1
import S1PreparedScalarErasureV1
import S1PreparedQueryErasureV1
import S1PreparedCompleteHashErasureV1
import S1RankTraceQueryScannerV1
import S1PreparedScratchCallsV1
import ClaimsUnrolledFinishAdapters
import PSem_Rows
import PSem_Shapes
import PSem_Expand
import PSem_Values
import PSem_Canonical
import PSem_FieldCanonical
import RawSourceDigestLog
import ExtractedSourceSemanticSampler
import RawSourceLiteralSamplerStep

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `CurrentPreparedOrdinaryRankV1, `CurrentPreparedJointRankPrefix, `CurrentPreparedJointRankTrace, `CurrentPreparedJointRankMeaning, `PreparedSourcePowersJointRankV1, `PreparedSourcePowersEntryV1, `PreparedParsedInactiveV1, `SelectedWideViewInactiveV1, `SelectedWideViewPreparedEntryV1, `CurrentCompactInstalledPreparationV1, `CurrentOriginalPreparedNativeV1, `CurrentOriginalPreparedCarrierTransportV1, `CurrentOriginalPreparedInstallationV1, `S1BorrowedClaimPreparedBoundaryV1, `S1BorrowedClaimFirstCallerV1, `S2OwnedCurrentCarrierV1, `S2OwnedSourceInstallationV1, `S2SdkOwnedInstallationV1, `S2SdkOwnedReachabilityV1, `S2SdkOwnedDecodedReuseV1, `S2SdkOwnedGuardBodyV1, `S2SdkReadyAcquireV1, `S2SdkReadyStateV1, `S2SdkProofGateModelV1, `S2SdkProofPrefixTotalV1, `S2SdkProofGateTotalV1, `S2SdkGateAdmittedImageV1, `S2SdkProofComparatorV1, `S2SdkProofPrefixParentV1, `S2FrameOperationsTotalV1, `S2SdkBorrowedEquivalenceV1, `S2SdkProofGateJoinV1, `S2SdkAdmittedCallerV1, `S2SdkLinkedCallerV1, `S2SdkErrorBufferFrameV1, `S2SdkFixedInputCallerV1, `S2SdkCheckpointWriterV1, `S2SdkSavedFirstV1, `S2SdkFixedSavedFirstV1, `S126SdkFixedInputCurrentV1, `S126SdkFixedSavedCurrentV1, `S2SdkMetadataFrameV1, `S126SdkSavedAccountExportV1, `S2SdkCheckpointImageV1, `S2SdkFixedImageFirstV1, `S2SdkKeyEqualityV1, `S6CurrentVerifierCarrierV1, `S1M31EmbeddingTotalV1, `S1QueryTraceEmbeddingV1, `S1OriginalPreparedSourceEmbeddingV1, `S1OriginalSerializerInstallationV1, `S1OriginalSerializedRankTraceV1, `S1BorrowedClaimConcreteCallerV1, `S1SemanticVerifyReachabilityV1, `S1SemanticFinishRootsV1, `S1SemanticRootCopyV1, `S1PreparedSourceEffectsV1, `S1PreparedHashEffectsV1, `S1PreparedHashCodeV1, `S1PreparedOracleCodeV1, `S1PreparedOracleProgramLawsV1, `S1QueryReadPairProgramV1, `S1QueryByteChainV1, `S1QueryPairEvaluationV1, `S1QueryProgramRelationV1, `S1PreparedSilentCodeV1, `S1PreparedHashErasureV1, `S1PreparedScalarEffectsV1, `S1PreparedQueryEffectsV1, `S1PreparedCodeLawsV1, `S1QueryMaterializeEffectsV1, `S1PreparedCodeProductLawsV1, `S1QueryMaterializePairsV1, `S1QueryMaterializeProgramV1, `S1QueryMaterializeModelV1, `S1QueryModelContinuationV1, `S1QueryFinishProgramV1, `S1QueryFinishAcceptedV1, `S1QueryPackEightExactV1, `S1QueryWordModelV1, `S1QueryScanModelStepV1, `S1QueryScanDriverModelV1, `S1QueryAbsorbProgramV1, `S1QueryByteChainBudgetV1, `S1QueryRow31ProgramV1, `S1PreparedScalarErasureV1, `S1PreparedQueryErasureV1, `S1PreparedCompleteHashErasureV1, `S1RankTraceQueryScannerV1, `S1PreparedScratchCallsV1, `ClaimsUnrolledFinishAdapters, `PSem_Rows, `PSem_Shapes, `PSem_Expand, `PSem_Values, `PSem_Canonical, `PSem_FieldCanonical, `RawSourceDigestLog, `ExtractedSourceSemanticSampler, `RawSourceLiteralSamplerStep ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ5_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ5_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ5_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ5_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ5_AUDIT_COMPLETE declarations={count} modules={selected.size}"
