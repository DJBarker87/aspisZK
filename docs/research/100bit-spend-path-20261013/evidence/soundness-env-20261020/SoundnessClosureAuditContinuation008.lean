import Lean
import R1LiteralSemanticViewComponents
import R1LiteralSemanticTake
import R1LiteralC1Prefix
import R1LiteralStageMessageCongr
import R1LiteralReadStability
import R1LiteralOpeningCoherence
import R1LiteralStageFacts
import R1LiteralReadAtFacts
import R1LiteralIndexedPrefix
import R1LiteralSemanticNoHit
import R1LiteralSemanticExcludedLift
import R1LiteralMatchingFacts
import R1LiteralMatchingSemanticData
import R1LiteralTerminalSpend
import R1LiteralOpeningBinding
import R1LiteralOpeningGood
import R1LiteralByteRunFacts
import R1LiteralGammaSample
import R1LiteralOpeningRunGood
import R1LiteralQueryReadFacts
import R1LiteralQueryBinding
import R1LiteralRhoBinding
import R1LiteralQueryCurrentRead
import R1LiteralQueryContext
import R1LiteralQueryRhoSupport
import R1LiteralQueryRhoTranscriptSupport
import R1LiteralPairingChecks
import R1LiteralTerminalRunSpend
import R1LiteralAcceptanceTerminal
import HchecksReaderComposition

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1LiteralSemanticViewComponents, `R1LiteralSemanticTake, `R1LiteralC1Prefix, `R1LiteralStageMessageCongr, `R1LiteralReadStability, `R1LiteralOpeningCoherence, `R1LiteralStageFacts, `R1LiteralReadAtFacts, `R1LiteralIndexedPrefix, `R1LiteralSemanticNoHit, `R1LiteralSemanticExcludedLift, `R1LiteralMatchingFacts, `R1LiteralMatchingSemanticData, `R1LiteralTerminalSpend, `R1LiteralOpeningBinding, `R1LiteralOpeningGood, `R1LiteralByteRunFacts, `R1LiteralGammaSample, `R1LiteralOpeningRunGood, `R1LiteralQueryReadFacts, `R1LiteralQueryBinding, `R1LiteralRhoBinding, `R1LiteralQueryCurrentRead, `R1LiteralQueryContext, `R1LiteralQueryRhoSupport, `R1LiteralQueryRhoTranscriptSupport, `R1LiteralPairingChecks, `R1LiteralTerminalRunSpend, `R1LiteralAcceptanceTerminal, `HchecksReaderComposition]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
