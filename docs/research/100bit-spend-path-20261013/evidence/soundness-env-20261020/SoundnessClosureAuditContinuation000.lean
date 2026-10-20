import Lean
import Stage2ContinuationTypes
import WireTx2BinaryBodies
import WireTx2Records
import WireTx2SliceFacts
import WireTx2LeafBodies
import WireTx2LeafCalls
import BinStage2FoldedWord
import WireTx2BinaryCalls
import R13WireToBin
import R13LeafSlices
import R13SourceTerminalBody
import R13SourceTerminal
import R13ConditionalOpening
import R22Stage2ControlBounds
import R22Stage2LocalBodies
import R22Stage2LeafTotal
import R22Stage2ReaderTotal
import R22Stage2OpeningTotal
import R22Stage2Audit
import Stage2FinishBody
import Stage2FinishControl
import Stage2ContinuationResumeBody
import Stage2ContinuationResume
import Stage2ContinuationQueryLoop
import Stage2ContinuationQueryAdvance
import Stage2ContinuationFacts
import Stage2QueryChecks
import Stage2AccumulatorStep
import Stage2FinishPairing
import Stage2FinishAccumulator

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`Stage2ContinuationTypes, `WireTx2BinaryBodies, `WireTx2Records, `WireTx2SliceFacts, `WireTx2LeafBodies, `WireTx2LeafCalls, `BinStage2FoldedWord, `WireTx2BinaryCalls, `R13WireToBin, `R13LeafSlices, `R13SourceTerminalBody, `R13SourceTerminal, `R13ConditionalOpening, `R22Stage2ControlBounds, `R22Stage2LocalBodies, `R22Stage2LeafTotal, `R22Stage2ReaderTotal, `R22Stage2OpeningTotal, `R22Stage2Audit, `Stage2FinishBody, `Stage2FinishControl, `Stage2ContinuationResumeBody, `Stage2ContinuationResume, `Stage2ContinuationQueryLoop, `Stage2ContinuationQueryAdvance, `Stage2ContinuationFacts, `Stage2QueryChecks, `Stage2AccumulatorStep, `Stage2FinishPairing, `Stage2FinishAccumulator]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
