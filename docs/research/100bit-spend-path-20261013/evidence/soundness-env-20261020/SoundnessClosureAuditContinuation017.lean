import Lean
import RawCutRecordedWordsExecutable
import RawCommitmentFrameReplay
import RawCommitmentFrameReplayCorrect
import RawCutWordsFromRunExecutable
import RawCompiledRunWordStabilityV8
import RawCompiledTranscriptRoundAlignmentV7
import RawChecksCommitmentFormats
import RawCompiledChecksOriginalSchedule
import RawChecksInjectionFormat
import RawChecksAdaptiveInjection
import RawCutWordsFromRunPublicValid
import RawRecordedPublicSpendExtractorCore
import RawRecordedPublicSpendExtractorPublicEquality
import RawRecordedPublicSpendExtractorReturnedRelation
import RawEnrichedOpeningWordIdentity
import RawRecordedChecksSpendExtractor
import RawRecordedPublicSpendExtractorCompleteness
import RawRecordedOracleExtractionMass
import RawRecordedActualAdaptiveFailureBoundV6
import RawChecksAdaptiveFailureConsumer
import RawChecksHitFromTransport
import RawChecksAdaptiveCleanModel
import RawChecksAdaptiveFailureNoModel
import RawExtractorCostLedger
import RawExtractorCostComposedV2
import SharedTensorContraction
import Stage2ContinuationParse
import Stage2ContinuationLoop
import Stage2ContinuationOwnedLoop
import Stage2FinishGeometry

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`RawCutRecordedWordsExecutable, `RawCommitmentFrameReplay, `RawCommitmentFrameReplayCorrect, `RawCutWordsFromRunExecutable, `RawCompiledRunWordStabilityV8, `RawCompiledTranscriptRoundAlignmentV7, `RawChecksCommitmentFormats, `RawCompiledChecksOriginalSchedule, `RawChecksInjectionFormat, `RawChecksAdaptiveInjection, `RawCutWordsFromRunPublicValid, `RawRecordedPublicSpendExtractorCore, `RawRecordedPublicSpendExtractorPublicEquality, `RawRecordedPublicSpendExtractorReturnedRelation, `RawEnrichedOpeningWordIdentity, `RawRecordedChecksSpendExtractor, `RawRecordedPublicSpendExtractorCompleteness, `RawRecordedOracleExtractionMass, `RawRecordedActualAdaptiveFailureBoundV6, `RawChecksAdaptiveFailureConsumer, `RawChecksHitFromTransport, `RawChecksAdaptiveCleanModel, `RawChecksAdaptiveFailureNoModel, `RawExtractorCostLedger, `RawExtractorCostComposedV2, `SharedTensorContraction, `Stage2ContinuationParse, `Stage2ContinuationLoop, `Stage2ContinuationOwnedLoop, `Stage2FinishGeometry]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
