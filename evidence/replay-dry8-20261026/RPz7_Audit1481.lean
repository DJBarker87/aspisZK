import Lean
import AspisR1PublicPreparation.Types
import AspisR1PublicPreparation.Funs
import ExtractedSemanticRoundsModel
import ExtractedPublicPreparationSuccess
import ExtractedPreparationSerializerFields
import ExtractedPreparationSerializerLoop
import ExtractedPreparationSerializerWhole
import ExtractedPublicPreparationBinding
import ExtractedFirstCallerReachability
import RepinS6First
import S6DecoderScopedReuseV1
import CurrentCompactFirstCompositionV1
import ExtractedPrefixParseCore
import ExtractedPreparedModel
import CurrentPreparedScratchModel
import CurrentPreparedScratchReachability
import ExtractedOpeningQueriesModel
import Query31SourceCalls
import S2OwnedCurrentCarrierV1
import S2OwnedSourceInstallationV1
import S2SdkOwnedInstallationV1
import S2SdkOwnedReachabilityV1
import S2SdkOwnedDecodedReuseV1
import S2SdkProofGateModelV1
import S2SdkProofPrefixTotalV1
import S2SdkProofGateTotalV1
import S2SdkProofComparatorV1
import S2SdkProofPrefixParentV1
import S2FrameOperationsTotalV1
import S2SdkBorrowedEquivalenceV1
import ExtractedTx1Model
import RPz7_PhaseIso
import RPz7_S1SemanticPhaseV1
import RPz7_S1SemanticPrefixModelV1
import RPz7_S1SemanticFinishModelV1
import RPz7_S1SemanticVerifyReachabilityV1
import RPz7_S1ExtractedRoundChildrenV1
import RPz7_S1SemanticFinishBoundsV1
import RPz7_ClaimsUnrolledFinish
import RPz7_NP6_StdModel
import RPz7_FIo_NativeTypes
import RPz7_FIo_NativeExternal
import RPz7_FIo_NativeFuns
import RPz7_ExtractedDigest32Transcript
import RPz7_ExtractedDigest32Callers
import RPz7_ExtractedDigest32SamplerTransport
import RPz7_SemanticCallSelectedCanonical
import RPz7_ExtractedDigest32Begin
import RPz7_ExtractedSemanticRoundsReachability
import RPz7_SemanticRoundAlphaSelectedCanonical
import RPz7_ActualBeginSelectedCanonical
import RPz7_S1SemanticProducerRangesV1
import RPz7_S1PreparedSourceStaticFieldsV1
import RPz7_CurrentCompactCallerConstantsV1
import RPz7_CurrentPreparedClaimCarriers
import RPz7_CurrentPreparedConcreteBoundaries
import RPz7_PreparedSourcePowersBoundariesV1
import RPz7_CurrentPreparedConcreteRun
import RPz7_CurrentPreparedSourceMeaning
import RPz7_CurrentPreparedPublicSources
import RPz7_CurrentPreparedOriginalPayload
import RPz7_CurrentPreparedGammaCallback
import RPz7_CurrentPreparedGammaSpecialization
import RPz7_CurrentPreparedGammaRank
import RPz7_CurrentSamplerPreparedCarrierBoundsV1
import RPz7_CurrentSamplerOrdinaryCallbackV2
import RPz7_CurrentPreparedScratchMeaning
import RPz7_CurrentPreparedCandidateSamplers
import RPz7_PreparedSourcePowersMeaningV1
import RPz7_PreparedFromQmSourceBridge
import RPz7_CurrentPreparedAlphaCanonical
import RPz7_CurrentPreparedRhoMeaning
import RPz7_ExtractedSourceFull25Frames
import RPz7_ExtractedSourceDigestAddresses
import RPz7_ExtractedSourceDigestOracle
import RPz7_Query31DigestInputBridge
import RPz7_Query31SourceOracleBridge
import RPz7_Query31MathematicalSchedule
import RPz7_Query31ConcreteMaterializedSchedule
import RPz7_Query31ConcreteMaterializedScheduleFull
import RPz7_CurrentPreparedConcreteQueryRho
import RPz7_CurrentPreparedSourceFromQm
import RPz7_CurrentPreparedInstalledMeaning

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `AspisR1PublicPreparation.Types, `AspisR1PublicPreparation.Funs, `ExtractedSemanticRoundsModel, `ExtractedPublicPreparationSuccess, `ExtractedPreparationSerializerFields, `ExtractedPreparationSerializerLoop, `ExtractedPreparationSerializerWhole, `ExtractedPublicPreparationBinding, `ExtractedFirstCallerReachability, `RepinS6First, `S6DecoderScopedReuseV1, `CurrentCompactFirstCompositionV1, `ExtractedPrefixParseCore, `ExtractedPreparedModel, `CurrentPreparedScratchModel, `CurrentPreparedScratchReachability, `ExtractedOpeningQueriesModel, `Query31SourceCalls, `S2OwnedCurrentCarrierV1, `S2OwnedSourceInstallationV1, `S2SdkOwnedInstallationV1, `S2SdkOwnedReachabilityV1, `S2SdkOwnedDecodedReuseV1, `S2SdkProofGateModelV1, `S2SdkProofPrefixTotalV1, `S2SdkProofGateTotalV1, `S2SdkProofComparatorV1, `S2SdkProofPrefixParentV1, `S2FrameOperationsTotalV1, `S2SdkBorrowedEquivalenceV1, `ExtractedTx1Model, `RPz7_PhaseIso, `RPz7_S1SemanticPhaseV1, `RPz7_S1SemanticPrefixModelV1, `RPz7_S1SemanticFinishModelV1, `RPz7_S1SemanticVerifyReachabilityV1, `RPz7_S1ExtractedRoundChildrenV1, `RPz7_S1SemanticFinishBoundsV1, `RPz7_ClaimsUnrolledFinish, `RPz7_NP6_StdModel, `RPz7_FIo_NativeTypes, `RPz7_FIo_NativeExternal, `RPz7_FIo_NativeFuns, `RPz7_ExtractedDigest32Transcript, `RPz7_ExtractedDigest32Callers, `RPz7_ExtractedDigest32SamplerTransport, `RPz7_SemanticCallSelectedCanonical, `RPz7_ExtractedDigest32Begin, `RPz7_ExtractedSemanticRoundsReachability, `RPz7_SemanticRoundAlphaSelectedCanonical, `RPz7_ActualBeginSelectedCanonical, `RPz7_S1SemanticProducerRangesV1, `RPz7_S1PreparedSourceStaticFieldsV1, `RPz7_CurrentCompactCallerConstantsV1, `RPz7_CurrentPreparedClaimCarriers, `RPz7_CurrentPreparedConcreteBoundaries, `RPz7_PreparedSourcePowersBoundariesV1, `RPz7_CurrentPreparedConcreteRun, `RPz7_CurrentPreparedSourceMeaning, `RPz7_CurrentPreparedPublicSources, `RPz7_CurrentPreparedOriginalPayload, `RPz7_CurrentPreparedGammaCallback, `RPz7_CurrentPreparedGammaSpecialization, `RPz7_CurrentPreparedGammaRank, `RPz7_CurrentSamplerPreparedCarrierBoundsV1, `RPz7_CurrentSamplerOrdinaryCallbackV2, `RPz7_CurrentPreparedScratchMeaning, `RPz7_CurrentPreparedCandidateSamplers, `RPz7_PreparedSourcePowersMeaningV1, `RPz7_PreparedFromQmSourceBridge, `RPz7_CurrentPreparedAlphaCanonical, `RPz7_CurrentPreparedRhoMeaning, `RPz7_ExtractedSourceFull25Frames, `RPz7_ExtractedSourceDigestAddresses, `RPz7_ExtractedSourceDigestOracle, `RPz7_Query31DigestInputBridge, `RPz7_Query31SourceOracleBridge, `RPz7_Query31MathematicalSchedule, `RPz7_Query31ConcreteMaterializedSchedule, `RPz7_Query31ConcreteMaterializedScheduleFull, `RPz7_CurrentPreparedConcreteQueryRho, `RPz7_CurrentPreparedSourceFromQm, `RPz7_CurrentPreparedInstalledMeaning ]
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
