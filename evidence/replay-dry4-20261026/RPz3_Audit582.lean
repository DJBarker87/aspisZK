import Lean
import R1ReseedSamplerLaw
import R1DuplexSamplers
import R1QuerySampler
import R1QuerySamplerBridge
import R1ParsedStateTrace
import R1OpeningReseedFrame
import R1ReseedBoundary
import R1PublicInitParse
import R1InitialWalk
import R1RawRoundDecode
import R1IndexedMessage
import R1RowZeroCodec
import R1CarryLast
import R1RawRoundCompletion
import R1PrefixAnswers
import R1JointPrefixAnswers
import R1JointNextLaw
import R1TranscriptView
import R1UnifiedSampler
import R1UnifiedSamplerLaw
import AspisV8R19.R572SequentialWordMass
import R1D18PointWeights
import R1D18OpeningWeights
import R1SelectedCircleWeightModel
import R1SelectedSemanticMessages
import R1SelectedFieldSequenceCodec
import R1CircleRecordCodec
import R1LengthFrameCodec
import R1OpeningRecordCodec
import R1SelectedIndexedRead
import R1SelectedPrefixRead
import R1SelectedOpeningStages
import R1SelectedOpeningClaims
import R1OpeningPolynomialView
import R1BackgroundOwnMap
import R1DecoderStateList
import R1TraceSuffixFacts
import R1InitialTrace
import R1BackgroundOutputMap
import R1InitialDecoder
import R1OpeningWalk
import R1PublicInitBoundaryFacts
import R1InitialWalkCells
import R1DuplexRecordPrefix
import R1DuplexRecordAnchor
import R1StrictReseedDecoder
import R1StrictReseedTrace
import R1ReseedPrefix
import R1ReseedSeparation
import R1OpeningWalkCells
import R1ReseedPrefixCells
import R1OpeningPrefixTrace
import R1RawRoundAppend
import R1OpeningPrefixCompletion
import R1JointContext
import R1BackgroundLawMap
import R1JointDecoder
import R1JointContextSound
import R1JointRecoveryTotal
import R1JointTranscriptView
import R1UnifiedInitialDecoder
import R1UnifiedRun
import R1UnifiedPayloadValue
import R1UnifiedRecords
import R1UnifiedPayloadStep
import R1UnifiedSteps
import R1UnifiedPhases
import R1RawRecordSplit
import R1UnifiedSemanticRecords
import R1UnifiedChainReads
import R1UnifiedProtocol
import R1UnifiedVerifier
import R1CompletedView
import R1UnifiedRecordCompletion
import R1UnifiedContinuation
import R1UnifiedQueryRun
import R1UnifiedQueryReads
import R1UnifiedTraceReads
import R1UnifiedPrefixedReads
import R1InitialWalkTrace
import R1UnifiedSemanticRecovery
import R1UnifiedSemanticContext
import R1PrefixNextLaw
import R1QueryMissingFacts
import R1TableStateSeparation
import R1PrefixPendingFacts
import R1PrefixRecordFacts
import R1PrefixRecordLength
import R1UnifiedSemanticDecoder
import R1UnifiedReseedDecoder
import R1UnifiedOpeningDecoder
import R1UnifiedSemanticLaw
import R1QueryBackgroundChain
import R1UnifiedQueryDecoder
import R1JointUnifiedDecoder
import R1UnifiedLabels
import R1PublicInitAbsorbSeparation
import R1UnifiedDecoder
import R1UnifiedInitialLaw
import R1UnifiedReseedLaw

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1ReseedSamplerLaw, `R1DuplexSamplers, `R1QuerySampler, `R1QuerySamplerBridge, `R1ParsedStateTrace, `R1OpeningReseedFrame, `R1ReseedBoundary, `R1PublicInitParse, `R1InitialWalk, `R1RawRoundDecode, `R1IndexedMessage, `R1RowZeroCodec, `R1CarryLast, `R1RawRoundCompletion, `R1PrefixAnswers, `R1JointPrefixAnswers, `R1JointNextLaw, `R1TranscriptView, `R1UnifiedSampler, `R1UnifiedSamplerLaw, `AspisV8R19.R572SequentialWordMass, `R1D18PointWeights, `R1D18OpeningWeights, `R1SelectedCircleWeightModel, `R1SelectedSemanticMessages, `R1SelectedFieldSequenceCodec, `R1CircleRecordCodec, `R1LengthFrameCodec, `R1OpeningRecordCodec, `R1SelectedIndexedRead, `R1SelectedPrefixRead, `R1SelectedOpeningStages, `R1SelectedOpeningClaims, `R1OpeningPolynomialView, `R1BackgroundOwnMap, `R1DecoderStateList, `R1TraceSuffixFacts, `R1InitialTrace, `R1BackgroundOutputMap, `R1InitialDecoder, `R1OpeningWalk, `R1PublicInitBoundaryFacts, `R1InitialWalkCells, `R1DuplexRecordPrefix, `R1DuplexRecordAnchor, `R1StrictReseedDecoder, `R1StrictReseedTrace, `R1ReseedPrefix, `R1ReseedSeparation, `R1OpeningWalkCells, `R1ReseedPrefixCells, `R1OpeningPrefixTrace, `R1RawRoundAppend, `R1OpeningPrefixCompletion, `R1JointContext, `R1BackgroundLawMap, `R1JointDecoder, `R1JointContextSound, `R1JointRecoveryTotal, `R1JointTranscriptView, `R1UnifiedInitialDecoder, `R1UnifiedRun, `R1UnifiedPayloadValue, `R1UnifiedRecords, `R1UnifiedPayloadStep, `R1UnifiedSteps, `R1UnifiedPhases, `R1RawRecordSplit, `R1UnifiedSemanticRecords, `R1UnifiedChainReads, `R1UnifiedProtocol, `R1UnifiedVerifier, `R1CompletedView, `R1UnifiedRecordCompletion, `R1UnifiedContinuation, `R1UnifiedQueryRun, `R1UnifiedQueryReads, `R1UnifiedTraceReads, `R1UnifiedPrefixedReads, `R1InitialWalkTrace, `R1UnifiedSemanticRecovery, `R1UnifiedSemanticContext, `R1PrefixNextLaw, `R1QueryMissingFacts, `R1TableStateSeparation, `R1PrefixPendingFacts, `R1PrefixRecordFacts, `R1PrefixRecordLength, `R1UnifiedSemanticDecoder, `R1UnifiedReseedDecoder, `R1UnifiedOpeningDecoder, `R1UnifiedSemanticLaw, `R1QueryBackgroundChain, `R1UnifiedQueryDecoder, `R1JointUnifiedDecoder, `R1UnifiedLabels, `R1PublicInitAbsorbSeparation, `R1UnifiedDecoder, `R1UnifiedInitialLaw, `R1UnifiedReseedLaw ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ3_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ3_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ3_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ3_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ3_AUDIT_COMPLETE declarations={count} modules={selected.size}"
