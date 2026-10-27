import Lean
import SAQ_Query
import SAQ_WideABI
import SAQ_RawCM
import SAQ_RawQM
import SAQ_RawWide
import SAQ_LineEmbedding
import SAQ_LineSource
import FIp_CircleSource
import FIp_CircleCuts
import FIp_CircleConstants
import FIp_CircleValue
import FIp_CircleMade
import FIp_CircleAlgebra
import SAQ_LineArrays
import SAQ_Arithmetic
import SAQ_MixedSource
import SAQ_QuerySource
import FIp_CircleQuery
import FIo_StringBounds
import AspisR1PublicPreparation.Types
import AspisR1PublicPreparation.Funs
import ExtractedSemanticRoundsModel
import S1ExtractedRoundChildrenV1
import ExtractedPublicPreparationSuccess
import ExtractedPreparationSerializerFields
import ExtractedPreparationSerializerLoop
import ExtractedPreparationSerializerWhole
import ExtractedPublicPreparationBinding
import ExtractedFirstCallerReachability
import RepinS6First
import S6DecoderScopedReuseV1
import CurrentCompactFirstCompositionV1
import S1SemanticPhaseV1
import ExtractedPrefixParseCore
import S1SemanticPrefixModelV1
import S1SemanticFinishModelV1
import S1SemanticFinishBoundsV1
import ClaimsUnrolledFinish
import NP6_StdModel
import FIo_NativeTypes
import FIo_QRawTypes
import FIo_QRawFuns
import FIo_NativeExternal
import FIo_NativeFuns
import FIn_WeightsTypes
import FIn_WeightsFuns
import FIn_ExtractTypes
import FIn_ExtractFuns
import SAG_DotTrace
import SAG_DotIndexed
import SAG_DotReader
import SAG_DotAdapter
import SAG_DotClosed
import F3M_ModelClaimShape
import F3_Model
import ExtractedDigest32Transcript
import ExtractedDigest32Callers
import ExtractedDigest32SamplerTransport
import SemanticCallSelectedCanonical
import ExtractedDigest32Begin
import ExtractedSemanticRoundsReachability
import SemanticRoundAlphaSelectedCanonical
import ActualBeginSelectedCanonical
import S1SemanticProducerRangesV1
import ExtractedPreparedModel
import CurrentPreparedScratchModel
import CurrentPreparedScratchReachability
import S1PreparedSourceStaticFieldsV1
import CurrentCompactCallerConstantsV1
import CurrentPreparedClaimCarriers
import CurrentPreparedConcreteBoundaries
import PreparedSourcePowersBoundariesV1
import CurrentPreparedConcreteRun
import CurrentPreparedSourceMeaning
import CurrentPreparedPublicSources
import CurrentPreparedOriginalPayload
import CurrentPreparedGammaCallback
import CurrentPreparedGammaSpecialization
import CurrentPreparedGammaRank
import CurrentSamplerPreparedCarrierBoundsV1
import CurrentSamplerOrdinaryCallbackV2
import CurrentPreparedScratchMeaning
import CurrentPreparedCandidateSamplers
import PreparedSourcePowersMeaningV1
import PreparedFromQmSourceBridge
import CurrentPreparedAlphaCanonical
import CurrentPreparedRhoMeaning
import ExtractedOpeningQueriesModel
import Query31SourceCalls
import ExtractedSourceFull25Frames
import ExtractedSourceDigestAddresses
import ExtractedSourceDigestOracle
import Query31DigestInputBridge
import Query31SourceOracleBridge
import Query31MathematicalSchedule
import Query31ConcreteMaterializedSchedule
import Query31ConcreteMaterializedScheduleFull
import CurrentPreparedConcreteQueryRho
import CurrentPreparedSourceFromQm
import CurrentPreparedInstalledMeaning

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `SAQ_Query, `SAQ_WideABI, `SAQ_RawCM, `SAQ_RawQM, `SAQ_RawWide, `SAQ_LineEmbedding, `SAQ_LineSource, `FIp_CircleSource, `FIp_CircleCuts, `FIp_CircleConstants, `FIp_CircleValue, `FIp_CircleMade, `FIp_CircleAlgebra, `SAQ_LineArrays, `SAQ_Arithmetic, `SAQ_MixedSource, `SAQ_QuerySource, `FIp_CircleQuery, `FIo_StringBounds, `AspisR1PublicPreparation.Types, `AspisR1PublicPreparation.Funs, `ExtractedSemanticRoundsModel, `S1ExtractedRoundChildrenV1, `ExtractedPublicPreparationSuccess, `ExtractedPreparationSerializerFields, `ExtractedPreparationSerializerLoop, `ExtractedPreparationSerializerWhole, `ExtractedPublicPreparationBinding, `ExtractedFirstCallerReachability, `RepinS6First, `S6DecoderScopedReuseV1, `CurrentCompactFirstCompositionV1, `S1SemanticPhaseV1, `ExtractedPrefixParseCore, `S1SemanticPrefixModelV1, `S1SemanticFinishModelV1, `S1SemanticFinishBoundsV1, `ClaimsUnrolledFinish, `NP6_StdModel, `FIo_NativeTypes, `FIo_QRawTypes, `FIo_QRawFuns, `FIo_NativeExternal, `FIo_NativeFuns, `FIn_WeightsTypes, `FIn_WeightsFuns, `FIn_ExtractTypes, `FIn_ExtractFuns, `SAG_DotTrace, `SAG_DotIndexed, `SAG_DotReader, `SAG_DotAdapter, `SAG_DotClosed, `F3M_ModelClaimShape, `F3_Model, `ExtractedDigest32Transcript, `ExtractedDigest32Callers, `ExtractedDigest32SamplerTransport, `SemanticCallSelectedCanonical, `ExtractedDigest32Begin, `ExtractedSemanticRoundsReachability, `SemanticRoundAlphaSelectedCanonical, `ActualBeginSelectedCanonical, `S1SemanticProducerRangesV1, `ExtractedPreparedModel, `CurrentPreparedScratchModel, `CurrentPreparedScratchReachability, `S1PreparedSourceStaticFieldsV1, `CurrentCompactCallerConstantsV1, `CurrentPreparedClaimCarriers, `CurrentPreparedConcreteBoundaries, `PreparedSourcePowersBoundariesV1, `CurrentPreparedConcreteRun, `CurrentPreparedSourceMeaning, `CurrentPreparedPublicSources, `CurrentPreparedOriginalPayload, `CurrentPreparedGammaCallback, `CurrentPreparedGammaSpecialization, `CurrentPreparedGammaRank, `CurrentSamplerPreparedCarrierBoundsV1, `CurrentSamplerOrdinaryCallbackV2, `CurrentPreparedScratchMeaning, `CurrentPreparedCandidateSamplers, `PreparedSourcePowersMeaningV1, `PreparedFromQmSourceBridge, `CurrentPreparedAlphaCanonical, `CurrentPreparedRhoMeaning, `ExtractedOpeningQueriesModel, `Query31SourceCalls, `ExtractedSourceFull25Frames, `ExtractedSourceDigestAddresses, `ExtractedSourceDigestOracle, `Query31DigestInputBridge, `Query31SourceOracleBridge, `Query31MathematicalSchedule, `Query31ConcreteMaterializedSchedule, `Query31ConcreteMaterializedScheduleFull, `CurrentPreparedConcreteQueryRho, `CurrentPreparedSourceFromQm, `CurrentPreparedInstalledMeaning ]
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
