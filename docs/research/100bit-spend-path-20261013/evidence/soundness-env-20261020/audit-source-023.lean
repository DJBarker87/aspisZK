import Lean
import R1SelectedOpeningEvents
import R1SelectedOpeningEventMass
import R1SelectedOpeningData
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
import R1SubfieldBatchStage2
import R1ResidualBatch
import R1NaturalEmbedding
import R1QueryAccumulator
import R1QueryResidualBridge
import R1RhoSamplerBound
import R1GenericPackBasis
import R1ConcretePackBasis
import R1GenericProgramRenameMass
import R1ProgramSamplerMap
import R1GenericNoHitFS2
import OracleProgramRecording
import OracleProgramReplay
import BinOpeningBinding
import WireBindingRecordCodec
import SharedBinaryRecordGrammar
import BinSharedGrammarBridge

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1SelectedOpeningEvents, `R1SelectedOpeningEventMass, `R1SelectedOpeningData, `R1UnifiedInitialLaw, `R1UnifiedReseedLaw, `R1UnifiedOpeningLaw, `R1QueryBackgroundLaw, `R1UnifiedQueryLaw, `R1JointUnifiedLaw, `R1JointUnifiedBound, `R1UnifiedDecoderBound, `R1UnifiedCausalBound, `R1UnifiedQueryDensity, `R1SubfieldBatchStage2, `R1ResidualBatch, `R1NaturalEmbedding, `R1QueryAccumulator, `R1QueryResidualBridge, `R1RhoSamplerBound, `R1GenericPackBasis, `R1ConcretePackBasis, `R1GenericProgramRenameMass, `R1ProgramSamplerMap, `R1GenericNoHitFS2, `OracleProgramRecording, `OracleProgramReplay, `BinOpeningBinding, `WireBindingRecordCodec, `SharedBinaryRecordGrammar, `BinSharedGrammarBridge]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
