import Lean
import R1ExtractedM31Parser
import AspisR72Sampler.Types
import AspisR72Sampler.Funs
import AspisV8R19.SamplerWordRead
import AspisV8R19.SqueezeSourceExecution
import AspisV8R19.DuplexFrames
import AspisV8R19.DuplexFreshPair
import AspisV8R19.SourceDuplexStep
import AspisV8R19.SqueezeOracleBridge
import AspisV8R19.SourceOraclePrograms
import AspisV8R19.SamplerWords
import AspisV8R19.SamplerWordBridge
import R1RetainedFieldByteCodec
import AeneasWordCodec
import R1M31ParserRefinement
import R1M31ParserCanonicality
import R1M31ParserArray
import R1CandidateParserSupport
import R1ParserArraySlice
import R1CandidateCM31Parser
import R1CandidateQM31Parser
import R1CandidateParserByteOrder
import R1CandidateStrictQM31Parser
import ActualDecodeKStrictQM31Parser
import AdaptiveStatementFiatShamir
import AdaptiveMembershipSoundness
import AspisV8R19.UniformStateFirstHit
import FS2.Duplex
import FS2.DuplexDecode
import FS2.DuplexDensity

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1ExtractedM31Parser, `AspisR72Sampler.Types, `AspisR72Sampler.Funs, `AspisV8R19.SamplerWordRead, `AspisV8R19.SqueezeSourceExecution, `AspisV8R19.DuplexFrames, `AspisV8R19.DuplexFreshPair, `AspisV8R19.SourceDuplexStep, `AspisV8R19.SqueezeOracleBridge, `AspisV8R19.SourceOraclePrograms, `AspisV8R19.SamplerWords, `AspisV8R19.SamplerWordBridge, `R1RetainedFieldByteCodec, `AeneasWordCodec, `R1M31ParserRefinement, `R1M31ParserCanonicality, `R1M31ParserArray, `R1CandidateParserSupport, `R1ParserArraySlice, `R1CandidateCM31Parser, `R1CandidateQM31Parser, `R1CandidateParserByteOrder, `R1CandidateStrictQM31Parser, `ActualDecodeKStrictQM31Parser, `AdaptiveStatementFiatShamir, `AdaptiveMembershipSoundness, `AspisV8R19.UniformStateFirstHit, `FS2.Duplex, `FS2.DuplexDecode, `FS2.DuplexDensity]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
