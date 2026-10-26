import Lean
open Lean Elab Command
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/M31RetryMassRational.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "M31RetryMassRational"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1RawFunctionalWeights.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1RawFunctionalWeights"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1SpendRelationMap.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1SpendRelationMap"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1OutputCopyLinks.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1OutputCopyLinks"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/Dot.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.Dot"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0P/SemDegFamilies.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0P.SemDegFamilies"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/PublicSerializerFieldsRefinement431.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "PublicSerializerFieldsRefinement431"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1InitialFrameNoMerkle.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1InitialFrameNoMerkle"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalReadCollision.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalReadCollision"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalPredictedRecovery.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalPredictedRecovery"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1CanonicalLogInputs.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1CanonicalLogInputs"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1MerkleTable.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1MerkleTable"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1TraceSuffixFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1TraceSuffixFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1UnifiedSemanticRecords.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1UnifiedSemanticRecords"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1InitialWalkTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1InitialWalkTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PrefixPendingFacts.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PrefixPendingFacts"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1OpeningWalkCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1OpeningWalkCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1ReseedPrefixCells.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1ReseedPrefixCells"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisV8R19/R402Q22IndependentLaw.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisV8R19.R402Q22IndependentLaw"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentPowersConcreteMul.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentPowersConcreteMul"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytes3ScalarShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytes3ScalarShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CheckpointBytes3WordMath.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CheckpointBytes3WordMath"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCkptAbiReadSequence.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCkptAbiReadSequence"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortCkptAbi2StdInventory.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortCkptAbi2StdInventory"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4C_RowMeaning.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4C_RowMeaning"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/P2P_FinishEffects.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "P2P_FinishEffects"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeRootGuard.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeRootGuard"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeCountPhysical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeCountPhysical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeCountBounds.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeCountBounds"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConePhysicalViews.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConePhysicalViews"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_TraceInput.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_TraceInput"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_TraceStart.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_TraceStart"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_TraceBytes0.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_TraceBytes0"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_TraceBytes1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_TraceBytes1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_TraceBytes2.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_TraceBytes2"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_TraceBytes3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_TraceBytes3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_ListWindow.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_ListWindow"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3P_DecodeLimbMeaning.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3P_DecodeLimbMeaning"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/AspisR1DecodeKFullLoopBodyValueFrame.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1DecodeKFullLoopBodyValueFrame"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_ModelClaimShape.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_ModelClaimShape"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_ClaimExpansion.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_ClaimExpansion"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_ClaimTerms.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_ClaimTerms"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/F3M_SevenTerms.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "F3M_SevenTerms"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/IndexedCandidateOuterByteBridgeV13.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "IndexedCandidateOuterByteBridgeV13"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R1PairCopyLinks.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R1PairCopyLinks"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisFormal/Pool/V7PairLeafOccupancy.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisFormal.Pool.V7PairLeafOccupancy"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1WideToBytesSource/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1WideToBytesSource.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1WideToBytesSource/FunsExternal.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1WideToBytesSource.FunsExternal"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1ClaimOwnedOuterCompleteV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1ClaimOwnedOuterCompleteV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6CurrentAdapterCarrierV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6CurrentAdapterCarrierV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6CurrentBoxedDecoderSourceV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6CurrentBoxedDecoderSourceV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S6OuterNativeDigestTotalV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S6OuterNativeDigestTotalV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/OraclePortFrozen2ActualChecks.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortFrozen2ActualChecks"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/Port4B_NativeLeaf.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "Port4B_NativeLeaf"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S3PowersCanonicalTraceV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S3PowersCanonicalTraceV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/StatefulArrayFromFnModelV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "StatefulArrayFromFnModelV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/GammaCallerDigitsModel.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GammaCallerDigitsModel"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/IndexedCandidateAddSmallNatModelV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "IndexedCandidateAddSmallNatModelV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1Post25SamplerIndexedAddSmallCandidate/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1Post25SamplerIndexedAddSmallCandidate.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedMaskPreparedState.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedMaskPreparedState"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedMaskCM31Mul.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedMaskCM31Mul"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimKappaPolynomial.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentClaimKappaPolynomial"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimHelperCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentClaimHelperCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1S5ClaimScalarFinishCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1S5ClaimScalarFinishCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FinishDotCountBoundV3.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinishDotCountBoundV3"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S5QRaw/EbyKPushDecodedProductUpdateV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S5QRaw.EbyKPushDecodedProductUpdateV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/EbyKPowerValueCanonicalToPushV5.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EbyKPowerValueCanonicalToPushV5"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1FinishDotReturnedDeltaDecodeV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1FinishDotReturnedDeltaDecodeV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1FinishDotReturnedFieldProductV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1FinishDotReturnedFieldProductV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimScalarBody.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentClaimScalarBody"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentFinishField.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentFinishField"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentClaimOuterTrace.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentClaimOuterTrace"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/FinishAcceptedRhsCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "FinishAcceptedRhsCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/EbyKNewToPushStateABI.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EbyKNewToPushStateABI"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentEbyFinishCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentEbyFinishCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/CurrentFinishArithmetic.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "CurrentFinishArithmetic"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/EbyKPushCheckedScalarCanonical.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "EbyKPushCheckedScalarCanonical"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/DotPushSuccessResidues.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "DotPushSuccessResidues"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/GExp_PreparedBlockAssociation.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "GExp_PreparedBlockAssociation"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedPreparationSerializerFields.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedPreparationSerializerFields"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/ExtractedDecoderPublicBridge.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "ExtractedDecoderPublicBridge"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofConeNodeDomain.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofConeNodeDomain"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/MultiproofSortRef/Types.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "MultiproofSortRef.Types"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/OraclePortActualAcceptanceC6.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "OraclePortActualAcceptanceC6"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/AspisR1DecodeKFullHelperCanonicality.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "AspisR1DecodeKFullHelperCanonicality"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryByteChainV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryByteChainV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryFinishAcceptedV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryFinishAcceptedV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryPackEightExactV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryPackEightExactV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1QueryRow31ProgramV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1QueryRow31ProgramV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/S1NativeCompactThreeRowsV1.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "S1NativeCompactThreeRowsV1"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/OpeningDefinitions.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.OpeningDefinitions"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/ListsResponses.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.ListsResponses"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R0/Round.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R0.Round"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17TableAChunk01Certificate.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17TableAChunk01Certificate"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17TableAChunk02Certificate.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17TableAChunk02Certificate"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17TableAChunk03Certificate.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17TableAChunk03Certificate"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17TableAChunk04Certificate.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17TableAChunk04Certificate"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17TableAChunk05Certificate.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17TableAChunk05Certificate"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17TableAChunk06Certificate.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17TableAChunk06Certificate"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd do
  let (data, _) ← liftIO <| readModuleData "/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects/R17TableAChunk07Certificate.olean"
  logInfo m!"RPZ4_HEADER {(Json.mkObj [("module", toJson "R17TableAChunk07Certificate"), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
run_cmd logInfo "RPZ4_HEADERS_COMPLETE"
