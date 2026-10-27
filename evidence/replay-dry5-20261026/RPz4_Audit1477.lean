import Lean
import R1SemanticRecordCodec
import R0C.CircleRows
import AspisV8R19.SamplerCirclePolicy
import R0P.CircleSampler
import R0P.SemAccept
import R0P.SemHonest
import R0P.SemDeg
import R0P.SemDegFamilies
import R0P.SemVirtualDeg
import R0P.SemPad
import R0C.SlackObstruction
import R0C.SlackBits
import R0C.V3.R0Q
import R0P.MessageDescent
import R0P.SemD3Glue
import R0P.MaskProtocol
import R0P.MaskView
import R1SemanticPayloadView
import R1LiteralSemanticPrefix
import R1SelectedSemanticPrefix
import R1SelectedSemanticPrefixFacts
import D18Transport
import R1D18Transport
import R1LiteralTypedContext
import R1OutputCopyLinks
import R1OutputNotes
import R1AppendNode
import R1PairCopyLinks
import AspisFormal.Pool.V7PairLeafOccupancy
import R1AppendPair
import R1InputPairCopyLinks
import R1InputPair
import R1SpendValues
import R1SpendSemantics
import R1InputPairSelection
import R1InputWitnessCore
import R1InputWitnessCheck
import R1AppendCopyLinks
import R1AppendPath
import SpendAppendBinding
import R1SpendAppendBinding
import SpendRelation
import R1SpendRelation
import R1SpendDataMap
import R1PublicBaseMap
import R1ExactBaseProjection
import R0P.SemD2Glue
import R0P.MaskD2
import R0P.MaskBadSets
import R0P.MaskDensity
import R0P.SemDuplexDecoder
import R0P.MaskDuplexDecoder
import R0P.MaskSource
import R0P.MaskD2Glue
import R0P.MaskValue
import R1LiteralSemanticView
import R1LiteralSemanticMessageFacts
import R1UnifiedSamplerLaw
import AspisV8R19.R572SequentialWordMass
import R1LiteralSemanticDensity
import R1LiteralOrdinaryDensity
import R1OpeningSamplerBound
import R1SelectedSamplerRanks
import R1SelectedChallengeMap
import R1LiteralCircleDensity
import R1LiteralChallengeRead
import R1LiteralCircleEvents
import R1RawFunctionalWeights
import R1RawPairing
import R1RawOpening
import R1D18PointWeights
import R1D18OpeningWeights
import R1SemanticOpening
import R1SemanticTransport
import R1SelectedCircleWeightModel
import R1SelectedOpeningFunctionals
import R1LiteralOpeningView
import R1SelectedSemanticMessages
import R1SelectedFieldSequenceCodec
import R1CircleRecordCodec
import R1LengthFrameCodec
import R1OpeningRecordCodec
import R1SelectedIndexedRead
import R1SelectedPrefixRead
import R1SelectedOpeningStages
import R1LiteralOpeningStages
import R1SelectedOpeningClaims
import R1OpeningPolynomialView
import R1SelectedOpeningEvents
import R1SelectedOpeningEventMass
import R1LiteralOpeningEvents
import R1LiteralOpeningDensity
import R1SelectedOpeningData
import R1LiteralMatchingData
import R1BackgroundOwnMap
import R1DecoderStateList
import R1TraceSuffixFacts
import R1InitialTrace
import R1BackgroundOutputMap
import R1InitialDecoder

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1SemanticRecordCodec, `R0C.CircleRows, `AspisV8R19.SamplerCirclePolicy, `R0P.CircleSampler, `R0P.SemAccept, `R0P.SemHonest, `R0P.SemDeg, `R0P.SemDegFamilies, `R0P.SemVirtualDeg, `R0P.SemPad, `R0C.SlackObstruction, `R0C.SlackBits, `R0C.V3.R0Q, `R0P.MessageDescent, `R0P.SemD3Glue, `R0P.MaskProtocol, `R0P.MaskView, `R1SemanticPayloadView, `R1LiteralSemanticPrefix, `R1SelectedSemanticPrefix, `R1SelectedSemanticPrefixFacts, `D18Transport, `R1D18Transport, `R1LiteralTypedContext, `R1OutputCopyLinks, `R1OutputNotes, `R1AppendNode, `R1PairCopyLinks, `AspisFormal.Pool.V7PairLeafOccupancy, `R1AppendPair, `R1InputPairCopyLinks, `R1InputPair, `R1SpendValues, `R1SpendSemantics, `R1InputPairSelection, `R1InputWitnessCore, `R1InputWitnessCheck, `R1AppendCopyLinks, `R1AppendPath, `SpendAppendBinding, `R1SpendAppendBinding, `SpendRelation, `R1SpendRelation, `R1SpendDataMap, `R1PublicBaseMap, `R1ExactBaseProjection, `R0P.SemD2Glue, `R0P.MaskD2, `R0P.MaskBadSets, `R0P.MaskDensity, `R0P.SemDuplexDecoder, `R0P.MaskDuplexDecoder, `R0P.MaskSource, `R0P.MaskD2Glue, `R0P.MaskValue, `R1LiteralSemanticView, `R1LiteralSemanticMessageFacts, `R1UnifiedSamplerLaw, `AspisV8R19.R572SequentialWordMass, `R1LiteralSemanticDensity, `R1LiteralOrdinaryDensity, `R1OpeningSamplerBound, `R1SelectedSamplerRanks, `R1SelectedChallengeMap, `R1LiteralCircleDensity, `R1LiteralChallengeRead, `R1LiteralCircleEvents, `R1RawFunctionalWeights, `R1RawPairing, `R1RawOpening, `R1D18PointWeights, `R1D18OpeningWeights, `R1SemanticOpening, `R1SemanticTransport, `R1SelectedCircleWeightModel, `R1SelectedOpeningFunctionals, `R1LiteralOpeningView, `R1SelectedSemanticMessages, `R1SelectedFieldSequenceCodec, `R1CircleRecordCodec, `R1LengthFrameCodec, `R1OpeningRecordCodec, `R1SelectedIndexedRead, `R1SelectedPrefixRead, `R1SelectedOpeningStages, `R1LiteralOpeningStages, `R1SelectedOpeningClaims, `R1OpeningPolynomialView, `R1SelectedOpeningEvents, `R1SelectedOpeningEventMass, `R1LiteralOpeningEvents, `R1LiteralOpeningDensity, `R1SelectedOpeningData, `R1LiteralMatchingData, `R1BackgroundOwnMap, `R1DecoderStateList, `R1TraceSuffixFacts, `R1InitialTrace, `R1BackgroundOutputMap, `R1InitialDecoder ]
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
