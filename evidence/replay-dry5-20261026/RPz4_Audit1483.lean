import Lean
import RawLatePublicSelector
import FullPublicSelection
import FullPublicEarlyCase
import R1UnifiedOpeningRecords
import R1OpeningEndpointCells
import RawPublicOpeningWalkCells
import RawPublicOpeningPrefixTrace
import RawPublicOpeningRecovery
import R1UnifiedQueryView
import FullPublicOpeningCase
import R1TableBeforeOrder
import RawPublicOpeningAnchor
import R1UnifiedPhaseRecords
import R1OpeningPrefixAnchor
import R1OpeningAnchorCells
import R1QueryAnswersFirstRead
import R1JointNextTrace
import R1OpeningQueryTrace
import R1UnifiedRecovery
import RawPublicRhoRecovery
import FullPublicRhoCasePublicAPI
import FullPublicTotalCase
import RawPublicSelectionLift
import LiteralLegacyRun
import R1ProgramLabelRestriction
import RawBoundedProgram
import R1UnifiedCanonicalLabels
import LiteralLegacyVerifierTrace
import TraceBadWitness
import RawBoundedCollision
import R1UnifiedDispatchAddress
import R1UnifiedInitialReads
import R1UnifiedInitialCase
import R1UnifiedOpeningRecovery
import R1UnifiedOpeningView
import R1UnifiedOpeningInjection
import R1UnifiedOpeningCase
import R1QueryChainTraceFacts
import R1PrefixQueryTrace
import R1UnifiedQueryInjection
import R1UnifiedQueryCase
import R1JointActualView
import R1UnifiedRhoInjection
import R1UnifiedExperimentInjection
import R1UnifiedRhoCase
import R1UnifiedDispatchCase
import R1UnifiedTotalCase
import LiteralLegacyDecoderCompletion
import RawLiteralDecoderCompletion
import RawFullPublicSelection
import LiteralDecoderPrefixRestore
import LiteralWordAgreement
import RawLiteralDecoderRestore
import RawByteCutTable
import TableLogRepresentative
import RawByteTableWords
import LiteralTableWordChoice
import LiteralTableChoiceRun
import RawCutLiteralInitialAdvanceRead
import RawCutLiteralSamplerOrder
import RawCutLiteralNextFrame
import RawCutLiteralRowZeroOrder
import RawCutLiteralReseedOrder
import RawCutLiteralQueryOrder
import RawCutLiteralQueryAdjacent
import RawCutLiteralAllFrames
import RawCutConstructedWords
import TraceAppend
import RawByteLaterTableWords
import RawCutLaterTableLiteralWords
import LiteralTableChoiceWords
import RawLiteralRecordedDecoder
import RawFullPublicRun
import RawCompiledTranscript
import R1TraceAppend
import R1FollowAppend
import RawLiteralCompiledDecoder
import RawCompiledDecoderCompletion
import RawAdaptiveCompiledCompletion
import OracleProgramLawExt
import RawCutCompilerLaw
import RawAdaptiveDecoderInjection
import RawCompiledChecksOriginalSchedule
import RawChecksInjectionFormat
import RawChecksAdaptiveInjection
import RawCutWordsFromRunPublicValid
import RawRecordedPublicSpendExtractorCore
import RawRecordedPublicSpendExtractorPublicEquality
import RawRecordedPublicSpendExtractorReturnedRelation
import GSByteJointSpendExtractorCompleteness
import LiteralCheckedByteSpendExtractor
import CanonicalCutSemanticRead
import RawEnrichedOpeningWordIdentity
import RawRecordedChecksSpendExtractor
import RawRecordedPublicSpendExtractorCompleteness
import LiteralFreshAttemptBound
import LiteralFreshAbortComposition
import LiteralFreshBankAbortComposition
import RawRecordedOracleExtractionMass
import RawAdaptiveClassifierStartBound

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RawLatePublicSelector, `FullPublicSelection, `FullPublicEarlyCase, `R1UnifiedOpeningRecords, `R1OpeningEndpointCells, `RawPublicOpeningWalkCells, `RawPublicOpeningPrefixTrace, `RawPublicOpeningRecovery, `R1UnifiedQueryView, `FullPublicOpeningCase, `R1TableBeforeOrder, `RawPublicOpeningAnchor, `R1UnifiedPhaseRecords, `R1OpeningPrefixAnchor, `R1OpeningAnchorCells, `R1QueryAnswersFirstRead, `R1JointNextTrace, `R1OpeningQueryTrace, `R1UnifiedRecovery, `RawPublicRhoRecovery, `FullPublicRhoCasePublicAPI, `FullPublicTotalCase, `RawPublicSelectionLift, `LiteralLegacyRun, `R1ProgramLabelRestriction, `RawBoundedProgram, `R1UnifiedCanonicalLabels, `LiteralLegacyVerifierTrace, `TraceBadWitness, `RawBoundedCollision, `R1UnifiedDispatchAddress, `R1UnifiedInitialReads, `R1UnifiedInitialCase, `R1UnifiedOpeningRecovery, `R1UnifiedOpeningView, `R1UnifiedOpeningInjection, `R1UnifiedOpeningCase, `R1QueryChainTraceFacts, `R1PrefixQueryTrace, `R1UnifiedQueryInjection, `R1UnifiedQueryCase, `R1JointActualView, `R1UnifiedRhoInjection, `R1UnifiedExperimentInjection, `R1UnifiedRhoCase, `R1UnifiedDispatchCase, `R1UnifiedTotalCase, `LiteralLegacyDecoderCompletion, `RawLiteralDecoderCompletion, `RawFullPublicSelection, `LiteralDecoderPrefixRestore, `LiteralWordAgreement, `RawLiteralDecoderRestore, `RawByteCutTable, `TableLogRepresentative, `RawByteTableWords, `LiteralTableWordChoice, `LiteralTableChoiceRun, `RawCutLiteralInitialAdvanceRead, `RawCutLiteralSamplerOrder, `RawCutLiteralNextFrame, `RawCutLiteralRowZeroOrder, `RawCutLiteralReseedOrder, `RawCutLiteralQueryOrder, `RawCutLiteralQueryAdjacent, `RawCutLiteralAllFrames, `RawCutConstructedWords, `TraceAppend, `RawByteLaterTableWords, `RawCutLaterTableLiteralWords, `LiteralTableChoiceWords, `RawLiteralRecordedDecoder, `RawFullPublicRun, `RawCompiledTranscript, `R1TraceAppend, `R1FollowAppend, `RawLiteralCompiledDecoder, `RawCompiledDecoderCompletion, `RawAdaptiveCompiledCompletion, `OracleProgramLawExt, `RawCutCompilerLaw, `RawAdaptiveDecoderInjection, `RawCompiledChecksOriginalSchedule, `RawChecksInjectionFormat, `RawChecksAdaptiveInjection, `RawCutWordsFromRunPublicValid, `RawRecordedPublicSpendExtractorCore, `RawRecordedPublicSpendExtractorPublicEquality, `RawRecordedPublicSpendExtractorReturnedRelation, `GSByteJointSpendExtractorCompleteness, `LiteralCheckedByteSpendExtractor, `CanonicalCutSemanticRead, `RawEnrichedOpeningWordIdentity, `RawRecordedChecksSpendExtractor, `RawRecordedPublicSpendExtractorCompleteness, `LiteralFreshAttemptBound, `LiteralFreshAbortComposition, `LiteralFreshBankAbortComposition, `RawRecordedOracleExtractionMass, `RawAdaptiveClassifierStartBound ]
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
