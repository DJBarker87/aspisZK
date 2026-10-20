import Lean
import AspisR1RecordParser.Types
import AspisR1RecordParser.Funs
import AspisR1RowShape.Types
import AspisR1RowShape.Funs
import AspisR1WithdrawalValidation.Types
import AspisR1WithdrawalValidation.Funs
import BatchedWeightsActualReducer
import BatchedWeightsFlushPrimitiveV2
import BatchedWeightsFlushLaneV8
import BatchedWeightsFlushLaneBindV3
import BatchedWeightsPushLoopAllPrefixV11
import BatchedWeightsPushOuterFlushV13
import BatchedWeightsPushOuterNoFlushV3
import R1LiteralTranscript
import CanonicalCutEnrichedTranscript
import BinCanonicalCutWords
import R1LiteralSemanticPrefix
import R1LiteralSemanticView
import R1LiteralSemanticMessageFacts
import R1LiteralSemanticDensity
import R1LiteralOrdinaryDensity
import R1LiteralCircleDensity
import R1LiteralChallengeRead
import R1LiteralCircleEvents
import R1LiteralOpeningView
import R1LiteralOpeningStages
import R1LiteralOpeningEvents
import R1LiteralOpeningDensity
import R1LiteralMatchingData
import R1LiteralQueryDensity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`AspisR1RecordParser.Types, `AspisR1RecordParser.Funs, `AspisR1RowShape.Types, `AspisR1RowShape.Funs, `AspisR1WithdrawalValidation.Types, `AspisR1WithdrawalValidation.Funs, `BatchedWeightsActualReducer, `BatchedWeightsFlushPrimitiveV2, `BatchedWeightsFlushLaneV8, `BatchedWeightsFlushLaneBindV3, `BatchedWeightsPushLoopAllPrefixV11, `BatchedWeightsPushOuterFlushV13, `BatchedWeightsPushOuterNoFlushV3, `R1LiteralTranscript, `CanonicalCutEnrichedTranscript, `BinCanonicalCutWords, `R1LiteralSemanticPrefix, `R1LiteralSemanticView, `R1LiteralSemanticMessageFacts, `R1LiteralSemanticDensity, `R1LiteralOrdinaryDensity, `R1LiteralCircleDensity, `R1LiteralChallengeRead, `R1LiteralCircleEvents, `R1LiteralOpeningView, `R1LiteralOpeningStages, `R1LiteralOpeningEvents, `R1LiteralOpeningDensity, `R1LiteralMatchingData, `R1LiteralQueryDensity]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
