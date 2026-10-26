import Lean
import R1SamplerLongDivision
import R1SamplerMachineBounds
import R1SamplerWord
import R1SamplerPass
import R1SamplerWordPass
import ExtractedQM31SamplerPass
import ExtractedQM31SamplerPassLoop
import ExtractedQM31SamplerDivision
import ExtractedQM31SamplerBytes
import R1SamplerAddDigits
import R1SamplerCarry
import R1SamplerDigits
import R1SamplerArithmetic
import R1SamplerAddBridge
import R1SamplerRanking
import R1SamplerNatModel
import R1SamplerRepeatedPass
import ExtractedQM31SamplerDigits
import ExtractedCurrentQM31Equality
import ExtractedQM31SamplerCarrier
import R1SamplerBlockRank
import R1SamplerByteWord
import R1SamplerBytePass
import R1SourceSamplerByteRank
import ExtractedQM31SamplerCorrect
import ExtractedDigest32SamplerTransport
import AspisR1SelectedMaskProbe.Types
import AspisR1SelectedMaskProbe.Funs
import ExtractedMaskM31AddSub
import ExtractedMaskTowerAdd
import SemanticCallSelectedCanonical
import ExtractedSemanticRoundsModel
import ExtractedDigest32Begin
import ExtractedSemanticRoundsReachability
import SemanticRoundAlphaSelectedCanonical
import ActualBeginSelectedCanonical
import AspisR1SemanticCallExtraction.Types
import AspisR1SemanticCallExtraction.Funs
import AspisR1DecodeKFullV10.Types
import DecodeKOptionDiscriminantBridge
import AspisR1DecodeKFullV10.Funs
import S1ExtractedRoundChildrenV1
import AspisR1DecodeKFullV10ParserCanonicality
import AspisR1DecodeKFullParserCanonicalityCMQ
import AspisR1DecodeKFullHelperCanonicality
import AspisR1DecodeKCanonicalArrayInvariant
import AspisR1DecodeKFullLoopBodyFrame
import OccupancyRangeTraversal
import AspisR1DecodeKFullLoopFuelCanonicality
import AspisR1DecodeKFullLoopBodyPendingFrame
import AspisR1DecodeKFullLoopPendingFuel
import AspisR1DecodeKFullSuccessCanonicality
import S1SemanticProducerRangesV1
import CurrentCompactCallerTypesV1
import CurrentCompactCallerModelV1
import CurrentCompactPrepareReachabilityV1
import CurrentCompactTx1ReachabilityV1
import ExtractedPublicPreparationSuccess
import ExtractedPreparationSerializerFields
import ExtractedPreparationSerializerLoop
import AspisR1WithdrawalCaller.Types
import AspisR1WithdrawalCaller.Funs
import ExtractedWithdrawalCallerSuccess
import AspisR1TerminalDecoder.Types
import AspisR1TerminalDecoder.FunsExternal
import AspisR1TerminalDecoder.Funs
import ExtractedTerminalDecoderSuccess
import ExtractedDecoderWithdrawalSuccess
import ExtractedDecoderCallerBridge
import ExtractedWithdrawalCallerCarrier
import ExtractedWithdrawalCallerPublic
import ExtractedDecoderPublicBridge
import ExtractedDecoderPublicBinding
import ExtractedPreparationSerializerWhole
import ExtractedPublicPreparationBinding
import ExtractedFirstCallerReachability
import RepinS6First
import S6DecoderScopedReuseV1
import CurrentCompactFirstCompositionV1
import S1SemanticPhaseV1
import AspisR1PrefixAggregateParser.Types
import AspisR1PrefixAggregateParser.Funs
import ExtractedPrefixParseCore
import AspisR1CurrentWide.Types
import AspisR1CurrentWide.Funs
import AspisR1QueryGeometryActual.Types
import AspisR1QueryGeometryActual.Funs
import FibrePointSuccessOutput
import FibrePointDecodedProduct
import R17MinimalReverseBits
import R17MinimalReverseBitsBridge
import R17TableExponentDomainBridge
import R17TableBasePowerProbe
import R17TableBasePowerBridge
import R17TableAChunk00Certificate
import R17NarrowFunsA00ChunkPower
import R17ArrayIndexMake
import R17ActualTableArrayIndexV1
import R17ActualTableEntriesIndices
import R17ActualA00IndexPower

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1SamplerLongDivision, `R1SamplerMachineBounds, `R1SamplerWord, `R1SamplerPass, `R1SamplerWordPass, `ExtractedQM31SamplerPass, `ExtractedQM31SamplerPassLoop, `ExtractedQM31SamplerDivision, `ExtractedQM31SamplerBytes, `R1SamplerAddDigits, `R1SamplerCarry, `R1SamplerDigits, `R1SamplerArithmetic, `R1SamplerAddBridge, `R1SamplerRanking, `R1SamplerNatModel, `R1SamplerRepeatedPass, `ExtractedQM31SamplerDigits, `ExtractedCurrentQM31Equality, `ExtractedQM31SamplerCarrier, `R1SamplerBlockRank, `R1SamplerByteWord, `R1SamplerBytePass, `R1SourceSamplerByteRank, `ExtractedQM31SamplerCorrect, `ExtractedDigest32SamplerTransport, `AspisR1SelectedMaskProbe.Types, `AspisR1SelectedMaskProbe.Funs, `ExtractedMaskM31AddSub, `ExtractedMaskTowerAdd, `SemanticCallSelectedCanonical, `ExtractedSemanticRoundsModel, `ExtractedDigest32Begin, `ExtractedSemanticRoundsReachability, `SemanticRoundAlphaSelectedCanonical, `ActualBeginSelectedCanonical, `AspisR1SemanticCallExtraction.Types, `AspisR1SemanticCallExtraction.Funs, `AspisR1DecodeKFullV10.Types, `DecodeKOptionDiscriminantBridge, `AspisR1DecodeKFullV10.Funs, `S1ExtractedRoundChildrenV1, `AspisR1DecodeKFullV10ParserCanonicality, `AspisR1DecodeKFullParserCanonicalityCMQ, `AspisR1DecodeKFullHelperCanonicality, `AspisR1DecodeKCanonicalArrayInvariant, `AspisR1DecodeKFullLoopBodyFrame, `OccupancyRangeTraversal, `AspisR1DecodeKFullLoopFuelCanonicality, `AspisR1DecodeKFullLoopBodyPendingFrame, `AspisR1DecodeKFullLoopPendingFuel, `AspisR1DecodeKFullSuccessCanonicality, `S1SemanticProducerRangesV1, `CurrentCompactCallerTypesV1, `CurrentCompactCallerModelV1, `CurrentCompactPrepareReachabilityV1, `CurrentCompactTx1ReachabilityV1, `ExtractedPublicPreparationSuccess, `ExtractedPreparationSerializerFields, `ExtractedPreparationSerializerLoop, `AspisR1WithdrawalCaller.Types, `AspisR1WithdrawalCaller.Funs, `ExtractedWithdrawalCallerSuccess, `AspisR1TerminalDecoder.Types, `AspisR1TerminalDecoder.FunsExternal, `AspisR1TerminalDecoder.Funs, `ExtractedTerminalDecoderSuccess, `ExtractedDecoderWithdrawalSuccess, `ExtractedDecoderCallerBridge, `ExtractedWithdrawalCallerCarrier, `ExtractedWithdrawalCallerPublic, `ExtractedDecoderPublicBridge, `ExtractedDecoderPublicBinding, `ExtractedPreparationSerializerWhole, `ExtractedPublicPreparationBinding, `ExtractedFirstCallerReachability, `RepinS6First, `S6DecoderScopedReuseV1, `CurrentCompactFirstCompositionV1, `S1SemanticPhaseV1, `AspisR1PrefixAggregateParser.Types, `AspisR1PrefixAggregateParser.Funs, `ExtractedPrefixParseCore, `AspisR1CurrentWide.Types, `AspisR1CurrentWide.Funs, `AspisR1QueryGeometryActual.Types, `AspisR1QueryGeometryActual.Funs, `FibrePointSuccessOutput, `FibrePointDecodedProduct, `R17MinimalReverseBits, `R17MinimalReverseBitsBridge, `R17TableExponentDomainBridge, `R17TableBasePowerProbe, `R17TableBasePowerBridge, `R17TableAChunk00Certificate, `R17NarrowFunsA00ChunkPower, `R17ArrayIndexMake, `R17ActualTableArrayIndexV1, `R17ActualTableEntriesIndices, `R17ActualA00IndexPower ]
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
