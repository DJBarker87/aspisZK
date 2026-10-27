import Lean
import RPz7_S1OriginalPreparedSourceEmbeddingV1
import RPz7_S1OriginalSerializerInstallationV1
import RPz7_S1OriginalSerializedRankTraceV1
import RPz7_S1BorrowedClaimConcreteCallerV1
import RPz7_S1CurrentOwnedConcreteJoinV1
import RPz7_S1PreparedActiveBoundariesV1
import RPz7_S1ClosedPreparationInstallationV1
import RPz7_S1OriginalNewStaticFieldsV1
import RPz7_S1WideViewVariantV1
import RPz7_S1ClosedPrepareProvenanceV1
import RPz7_S1SemanticCarrierV1
import RPz7_S1SemanticFinishRootsV1
import RPz7_S1SemanticRootCopyV1
import RPz7_S1SemanticInstallationV1
import RPz7_S1AcceptedSemanticNumericV1
import RPz7_S1AcceptedChallengesNumericV1
import RPz7_S1WideViewSemanticV1
import RPz7_S1SemanticAlphaV1
import RPz7_S1PrepareSemanticRootsV1
import RPz7_S1NativePrepareBuffersV1
import RPz7_S1NativePreparePhysicalRootV1
import RPz7_S1ParsedSecondRootBytesV1
import RPz7_S1NativePreparePhysicalRootsV1
import RPz7_S1NativeOwnedStage1PhysicalRootV1
import RPz7_S1NativeOwnedStage1PhysicalRootsV1
import RPz7_S1ValuesOwnedStage1RootsV1
import RPz7_S1WideViewY1V1
import RPz7_S1ClosedPrepareRangesV1
import RPz7_S1ClaimY1ReadsV1
import RPz7_S1ValuesOwnedPrepareViewY1V1
import RPz7_S1ValuesOwnedStage1ViewY1V1
import RPz7_S1OwnedStage1ExtractedChildrenV1
import RPz7_S1OwnedStage1NumericV1
import RPz7_S1NativeBufferClaimTraceV1
import RPz7_S1PreparedSourceEffectsV1
import RPz7_S1PreparedHashEffectsV1
import RPz7_S1PreparedHashCodeV1
import RPz7_S1PreparedOracleCodeV1
import RPz7_S1PreparedOracleProgramLawsV1
import RPz7_S1QueryReadPairProgramV1
import RPz7_S1QueryByteChainV1
import RPz7_S1QueryPairEvaluationV1
import RPz7_S1QueryProgramRelationV1
import RPz7_S1PreparedSilentCodeV1
import RPz7_S1PreparedHashErasureV1
import RPz7_S1PreparedScalarEffectsV1
import RPz7_S1PreparedQueryEffectsV1
import RPz7_S1PreparedCodeLawsV1
import RPz7_S1QueryMaterializeEffectsV1
import RPz7_S1PreparedCodeProductLawsV1
import RPz7_S1QueryMaterializePairsV1
import RPz7_S1QueryMaterializeProgramV1
import RPz7_S1QueryMaterializeModelV1
import RPz7_S1QueryModelContinuationV1
import RPz7_S1QueryFinishProgramV1
import RPz7_S1QueryFinishAcceptedV1
import RPz7_S1QueryPackEightExactV1
import RPz7_S1QueryWordModelV1
import RPz7_S1QueryScanModelStepV1
import RPz7_S1QueryScanDriverModelV1
import RPz7_S1QueryAbsorbProgramV1
import RPz7_S1QueryByteChainBudgetV1
import RPz7_S1QueryRow31ProgramV1
import RPz7_S1PreparedScalarErasureV1
import RPz7_S1PreparedQueryErasureV1
import RPz7_S1PreparedCompleteHashErasureV1
import RPz7_S1ClosedPreparationHashCodeV1
import RPz7_S1QueryFixedProgramV1
import RPz7_S1QueryPairedBindV1
import RPz7_S1QueryClosedRelationV1
import RPz7_S1QueryEventTransportV1
import RPz7_S1RankTraceQueryScannerV1
import RPz7_S1RankTraceQueryProgramV1
import RPz7_S1PreparedScratchCallsV1
import RPz7_S1NativeBufferPreparedTraceV1
import RPz7_S1PrepareNumericV1
import RPz7_S6CurrentStage1FirstFieldsV1
import RPz7_S1OwnedStage1AccountNumericV1
import RPz7_SInt2_S6SdkStage1ReuseFactoredV1
import RPz7_SInt2_S1SdkStage1AccountNumericV1
import RPz7_SInt2_S6SdkSourceCutReuseV1
import RPz7_SInt2_S6SdkEnclosingCutsV1
import RPz7_SInt2_S1SdkSourceCutNumericV1
import RPz7_SInt2_S6SdkOriginalObjectCallerV1

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_S1OriginalPreparedSourceEmbeddingV1, `RPz7_S1OriginalSerializerInstallationV1, `RPz7_S1OriginalSerializedRankTraceV1, `RPz7_S1BorrowedClaimConcreteCallerV1, `RPz7_S1CurrentOwnedConcreteJoinV1, `RPz7_S1PreparedActiveBoundariesV1, `RPz7_S1ClosedPreparationInstallationV1, `RPz7_S1OriginalNewStaticFieldsV1, `RPz7_S1WideViewVariantV1, `RPz7_S1ClosedPrepareProvenanceV1, `RPz7_S1SemanticCarrierV1, `RPz7_S1SemanticFinishRootsV1, `RPz7_S1SemanticRootCopyV1, `RPz7_S1SemanticInstallationV1, `RPz7_S1AcceptedSemanticNumericV1, `RPz7_S1AcceptedChallengesNumericV1, `RPz7_S1WideViewSemanticV1, `RPz7_S1SemanticAlphaV1, `RPz7_S1PrepareSemanticRootsV1, `RPz7_S1NativePrepareBuffersV1, `RPz7_S1NativePreparePhysicalRootV1, `RPz7_S1ParsedSecondRootBytesV1, `RPz7_S1NativePreparePhysicalRootsV1, `RPz7_S1NativeOwnedStage1PhysicalRootV1, `RPz7_S1NativeOwnedStage1PhysicalRootsV1, `RPz7_S1ValuesOwnedStage1RootsV1, `RPz7_S1WideViewY1V1, `RPz7_S1ClosedPrepareRangesV1, `RPz7_S1ClaimY1ReadsV1, `RPz7_S1ValuesOwnedPrepareViewY1V1, `RPz7_S1ValuesOwnedStage1ViewY1V1, `RPz7_S1OwnedStage1ExtractedChildrenV1, `RPz7_S1OwnedStage1NumericV1, `RPz7_S1NativeBufferClaimTraceV1, `RPz7_S1PreparedSourceEffectsV1, `RPz7_S1PreparedHashEffectsV1, `RPz7_S1PreparedHashCodeV1, `RPz7_S1PreparedOracleCodeV1, `RPz7_S1PreparedOracleProgramLawsV1, `RPz7_S1QueryReadPairProgramV1, `RPz7_S1QueryByteChainV1, `RPz7_S1QueryPairEvaluationV1, `RPz7_S1QueryProgramRelationV1, `RPz7_S1PreparedSilentCodeV1, `RPz7_S1PreparedHashErasureV1, `RPz7_S1PreparedScalarEffectsV1, `RPz7_S1PreparedQueryEffectsV1, `RPz7_S1PreparedCodeLawsV1, `RPz7_S1QueryMaterializeEffectsV1, `RPz7_S1PreparedCodeProductLawsV1, `RPz7_S1QueryMaterializePairsV1, `RPz7_S1QueryMaterializeProgramV1, `RPz7_S1QueryMaterializeModelV1, `RPz7_S1QueryModelContinuationV1, `RPz7_S1QueryFinishProgramV1, `RPz7_S1QueryFinishAcceptedV1, `RPz7_S1QueryPackEightExactV1, `RPz7_S1QueryWordModelV1, `RPz7_S1QueryScanModelStepV1, `RPz7_S1QueryScanDriverModelV1, `RPz7_S1QueryAbsorbProgramV1, `RPz7_S1QueryByteChainBudgetV1, `RPz7_S1QueryRow31ProgramV1, `RPz7_S1PreparedScalarErasureV1, `RPz7_S1PreparedQueryErasureV1, `RPz7_S1PreparedCompleteHashErasureV1, `RPz7_S1ClosedPreparationHashCodeV1, `RPz7_S1QueryFixedProgramV1, `RPz7_S1QueryPairedBindV1, `RPz7_S1QueryClosedRelationV1, `RPz7_S1QueryEventTransportV1, `RPz7_S1RankTraceQueryScannerV1, `RPz7_S1RankTraceQueryProgramV1, `RPz7_S1PreparedScratchCallsV1, `RPz7_S1NativeBufferPreparedTraceV1, `RPz7_S1PrepareNumericV1, `RPz7_S6CurrentStage1FirstFieldsV1, `RPz7_S1OwnedStage1AccountNumericV1, `RPz7_SInt2_S6SdkStage1ReuseFactoredV1, `RPz7_SInt2_S1SdkStage1AccountNumericV1, `RPz7_SInt2_S6SdkSourceCutReuseV1, `RPz7_SInt2_S6SdkEnclosingCutsV1, `RPz7_SInt2_S1SdkSourceCutNumericV1, `RPz7_SInt2_S6SdkOriginalObjectCallerV1 ]
  let phaseOwners : Array Name := #[ `RPz7_S1SemanticPrefixModelV1, `RPz7_S1SemanticFinishModelV1, `RPz7_S1SemanticFinishBoundsV1, `RPz7_ClaimsUnrolledFinish, `RPz7_S1SemanticVerifyReachabilityV1, `RPz7_S1SemanticFinishRootsV1, `RPz7_S1AcceptedSemanticNumericV1, `RPz7_S1AcceptedChallengesNumericV1, `RPz7_S1SemanticCodeFinishV1, `RPz7_S1SemanticCodeVerifyV1, `RPz7_S1SemanticCodeFinishExactV1, `RPz7_S1SemanticCodeVerifyExactV1, `RPz7_GExp_FinishAssociation, `RPz7_GExp_VerifyAssociation, `RPz7_S1SemanticBudgetV1, `RPz7_AuS1_Semantic3, `RPz7_F3V_SemanticFinish, `RPz7_F3V_SemanticVerify, `RPz7_RawJ_VerifyRead, `RPz7_RawK_VerifyHead, `RPz7_F3U_VerifyHead ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ7_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ7_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ7_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        if phaseOwners.contains owner || n.toString.startsWith "RPz7_PhaseIso" || n.toString == "AspisR1.Rc10_Top.deployed" then
          logInfo m!"RPZ7_KERNEL_TYPE {(Json.mkObj [("name", toJson n.toString), ("type", toJson (repr c.type).pretty)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ7_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ7_AUDIT_COMPLETE declarations={count} modules={selected.size}"
