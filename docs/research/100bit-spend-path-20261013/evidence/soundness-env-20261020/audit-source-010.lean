import Lean
import R0C.SlackDensity
import R0C.V3.DuplexQ
import R0C.V3.DuplexQDensity
import R0C.V3.DQChain
import R0C.V3.DQDecodes
import R1QueryDecoderAnswers
import R1BackgroundMeanCongr
import R1QueryNextLaw
import R1InitialSamplerLaw
import R1TrailingStateFrame
import R1PublicInitFrame
import R1TraceSuffixFacts
import R1InitialTrace
import R1PrefixedStateCodec
import R1PublicInitParse
import R1BackgroundOutputMap
import R1InitialDecoder
import R1ParsedStateCollision
import R1ParsedStateTrace
import R1OpeningReseedFrame
import R1ReseedBoundary
import R1InitialWalk
import R1OpeningWalk
import R1PublicInitBoundaryFacts
import R1InitialWalkCells
import R1DuplexRecordPrefix
import R1DuplexRecordAnchor
import R1StrictReseedDecoder
import R1StrictReseedTrace
import R1CarryLast

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R0C.SlackDensity, `R0C.V3.DuplexQ, `R0C.V3.DuplexQDensity, `R0C.V3.DQChain, `R0C.V3.DQDecodes, `R1QueryDecoderAnswers, `R1BackgroundMeanCongr, `R1QueryNextLaw, `R1InitialSamplerLaw, `R1TrailingStateFrame, `R1PublicInitFrame, `R1TraceSuffixFacts, `R1InitialTrace, `R1PrefixedStateCodec, `R1PublicInitParse, `R1BackgroundOutputMap, `R1InitialDecoder, `R1ParsedStateCollision, `R1ParsedStateTrace, `R1OpeningReseedFrame, `R1ReseedBoundary, `R1InitialWalk, `R1OpeningWalk, `R1PublicInitBoundaryFacts, `R1InitialWalkCells, `R1DuplexRecordPrefix, `R1DuplexRecordAnchor, `R1StrictReseedDecoder, `R1StrictReseedTrace, `R1CarryLast]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
