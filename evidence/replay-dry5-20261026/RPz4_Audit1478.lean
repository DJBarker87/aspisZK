import Lean
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
import R1UnifiedOpeningLaw
import R1QueryBackgroundLaw
import R1UnifiedQueryLaw
import R1JointUnifiedLaw
import R1JointUnifiedBound
import R1UnifiedDecoderBound
import R1UnifiedCausalBound
import R1UnifiedQueryDensity
import R1LiteralQueryDensity
import R1LiteralQueryRead
import R1SubfieldBatchStage2
import R1ResidualBatch
import R1NaturalEmbedding
import R1QueryAccumulator
import R1QueryResidualBridge
import R1RhoSamplerBound
import R1LiteralRhoDensity
import R1GenericPackBasis
import R1ConcretePackBasis
import R1GenericProgramRenameMass
import R1ProgramSamplerMap
import R1LiteralByteSampler
import R1LiteralClassifier
import R1LiteralRun
import R1GenericNoHit
import R1GenericNoHitFS2
import R1LiteralProtocol
import R1LiteralByteProtocol
import RawCutTranscriptRun
import OracleProgramRecording
import AllAddressFiatShamirOutside
import AdaptiveStatementFiatShamir
import RawCutProverCompiler
import OracleDecisionFeasibilityCore
import BackgroundAddressMap
import BackgroundCanonicalLabels
import UnifiedDecoderCanonical
import PartialAddressTrace
import BackgroundAddressFollow
import BackgroundAddressRestriction

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1OpeningWalk, `R1PublicInitBoundaryFacts, `R1InitialWalkCells, `R1DuplexRecordPrefix, `R1DuplexRecordAnchor, `R1StrictReseedDecoder, `R1StrictReseedTrace, `R1ReseedPrefix, `R1ReseedSeparation, `R1OpeningWalkCells, `R1ReseedPrefixCells, `R1OpeningPrefixTrace, `R1RawRoundAppend, `R1OpeningPrefixCompletion, `R1JointContext, `R1BackgroundLawMap, `R1JointDecoder, `R1JointContextSound, `R1JointRecoveryTotal, `R1JointTranscriptView, `R1UnifiedInitialDecoder, `R1UnifiedRun, `R1UnifiedPayloadValue, `R1UnifiedRecords, `R1UnifiedPayloadStep, `R1UnifiedSteps, `R1UnifiedPhases, `R1RawRecordSplit, `R1UnifiedSemanticRecords, `R1UnifiedChainReads, `R1UnifiedProtocol, `R1UnifiedVerifier, `R1CompletedView, `R1UnifiedRecordCompletion, `R1UnifiedContinuation, `R1UnifiedQueryRun, `R1UnifiedQueryReads, `R1UnifiedTraceReads, `R1UnifiedPrefixedReads, `R1InitialWalkTrace, `R1UnifiedSemanticRecovery, `R1UnifiedSemanticContext, `R1PrefixNextLaw, `R1QueryMissingFacts, `R1TableStateSeparation, `R1PrefixPendingFacts, `R1PrefixRecordFacts, `R1PrefixRecordLength, `R1UnifiedSemanticDecoder, `R1UnifiedReseedDecoder, `R1UnifiedOpeningDecoder, `R1UnifiedSemanticLaw, `R1QueryBackgroundChain, `R1UnifiedQueryDecoder, `R1JointUnifiedDecoder, `R1UnifiedLabels, `R1PublicInitAbsorbSeparation, `R1UnifiedDecoder, `R1UnifiedInitialLaw, `R1UnifiedReseedLaw, `R1UnifiedOpeningLaw, `R1QueryBackgroundLaw, `R1UnifiedQueryLaw, `R1JointUnifiedLaw, `R1JointUnifiedBound, `R1UnifiedDecoderBound, `R1UnifiedCausalBound, `R1UnifiedQueryDensity, `R1LiteralQueryDensity, `R1LiteralQueryRead, `R1SubfieldBatchStage2, `R1ResidualBatch, `R1NaturalEmbedding, `R1QueryAccumulator, `R1QueryResidualBridge, `R1RhoSamplerBound, `R1LiteralRhoDensity, `R1GenericPackBasis, `R1ConcretePackBasis, `R1GenericProgramRenameMass, `R1ProgramSamplerMap, `R1LiteralByteSampler, `R1LiteralClassifier, `R1LiteralRun, `R1GenericNoHit, `R1GenericNoHitFS2, `R1LiteralProtocol, `R1LiteralByteProtocol, `RawCutTranscriptRun, `OracleProgramRecording, `AllAddressFiatShamirOutside, `AdaptiveStatementFiatShamir, `RawCutProverCompiler, `OracleDecisionFeasibilityCore, `BackgroundAddressMap, `BackgroundCanonicalLabels, `UnifiedDecoderCanonical, `PartialAddressTrace, `BackgroundAddressFollow, `BackgroundAddressRestriction ]
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
