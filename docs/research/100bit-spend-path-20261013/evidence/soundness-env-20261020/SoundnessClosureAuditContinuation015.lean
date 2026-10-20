import Lean
import LiteralComputedCandidateExtract
import GSByteJointSpendExtractor
import GSByteJointSpendExtractorCompleteness
import LiteralAdaptiveClassifierHitToDecodedChain
import LiteralCheckedByteSpendExtractor
import LiteralDecoderPrefixRestore
import LiteralFreshAttemptBound
import LiteralFreshAbortComposition
import LiteralFreshBankAbortComposition
import LiteralLegacyRun
import LiteralLegacyVerifierTrace
import LiteralLegacyDecoderCompletion
import LiteralNoHitFromTranscriptAlignment
import RawByteTableWords
import LiteralTableWordChoice
import LiteralTableChoiceRun
import RawCutLiteralStateSuccessor
import RawCutLiteralTranscriptSuccessor
import RawCutLiteralInitialAdvanceRead
import RawCutLiteralSamplerOrder
import RawCutLiteralNextFrame
import RawCutLiteralRowZeroOrder
import RawCutLiteralReseedOrder
import RawCutLiteralQueryAdjacent
import RawCutLiteralAllFrames
import RawCutCommitmentFrames
import RawCutConstructedWords
import RawByteLaterTableWords
import RawCutLaterTableLiteralWords
import LiteralTableChoiceWords

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`LiteralComputedCandidateExtract, `GSByteJointSpendExtractor, `GSByteJointSpendExtractorCompleteness, `LiteralAdaptiveClassifierHitToDecodedChain, `LiteralCheckedByteSpendExtractor, `LiteralDecoderPrefixRestore, `LiteralFreshAttemptBound, `LiteralFreshAbortComposition, `LiteralFreshBankAbortComposition, `LiteralLegacyRun, `LiteralLegacyVerifierTrace, `LiteralLegacyDecoderCompletion, `LiteralNoHitFromTranscriptAlignment, `RawByteTableWords, `LiteralTableWordChoice, `LiteralTableChoiceRun, `RawCutLiteralStateSuccessor, `RawCutLiteralTranscriptSuccessor, `RawCutLiteralInitialAdvanceRead, `RawCutLiteralSamplerOrder, `RawCutLiteralNextFrame, `RawCutLiteralRowZeroOrder, `RawCutLiteralReseedOrder, `RawCutLiteralQueryAdjacent, `RawCutLiteralAllFrames, `RawCutCommitmentFrames, `RawCutConstructedWords, `RawByteLaterTableWords, `RawCutLaterTableLiteralWords, `LiteralTableChoiceWords]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
