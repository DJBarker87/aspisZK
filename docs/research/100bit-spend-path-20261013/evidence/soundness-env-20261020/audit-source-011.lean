import Lean
import R1ReseedPrefix
import R1ReseedSeparation
import R1OpeningWalkCells
import R1ReseedPrefixCells
import R1OpeningPrefixTrace
import R1RawRoundDecode
import R1RawRoundCompletion
import R1RawRoundAppend
import R1PrefixAnswers
import R1OpeningPrefixCompletion
import R1IndexedMessage
import R1JointContext
import R1JointPrefixAnswers
import R1JointNextLaw
import R1BackgroundLawMap
import R1JointDecoder
import R1JointContextSound
import R1JointRecoveryTotal
import R1UnifiedSamplerPublic
import R1ReseedSamplerLaw
import R1DuplexSamplers
import R1QuerySampler
import R1QuerySamplerBridge
import R1RowZeroCodec
import R1TranscriptView
import R1UnifiedSampler
import R1UnifiedSamplerLaw
import R1JointTranscriptView
import R1UnifiedInitialDecoder
import R1UnifiedRun

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1ReseedPrefix, `R1ReseedSeparation, `R1OpeningWalkCells, `R1ReseedPrefixCells, `R1OpeningPrefixTrace, `R1RawRoundDecode, `R1RawRoundCompletion, `R1RawRoundAppend, `R1PrefixAnswers, `R1OpeningPrefixCompletion, `R1IndexedMessage, `R1JointContext, `R1JointPrefixAnswers, `R1JointNextLaw, `R1BackgroundLawMap, `R1JointDecoder, `R1JointContextSound, `R1JointRecoveryTotal, `R1UnifiedSamplerPublic, `R1ReseedSamplerLaw, `R1DuplexSamplers, `R1QuerySampler, `R1QuerySamplerBridge, `R1RowZeroCodec, `R1TranscriptView, `R1UnifiedSampler, `R1UnifiedSamplerLaw, `R1JointTranscriptView, `R1UnifiedInitialDecoder, `R1UnifiedRun]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
