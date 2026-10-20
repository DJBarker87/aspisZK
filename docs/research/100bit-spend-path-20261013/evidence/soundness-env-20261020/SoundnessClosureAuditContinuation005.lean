import Lean
import R1LiteralQueryRead
import R1LiteralRhoDensity
import R1LiteralByteSampler
import R1LiteralClassifier
import R1LiteralRun
import R1LiteralProtocol
import R1LiteralByteProtocol
import RawCutTranscriptRun
import RawCutProverCompiler
import RawCutWordsFromView
import BinCompiledRunWordStability
import RawSamplerSuffixCorrespondence
import BinThreeCommitmentTypedOpening
import BinSourceCommitmentWords
import BinWirePublicLengths
import ExtractedTerminalDecoderSuccess
import BinWireEnvelopeLengths
import BinWireBindingLengths
import RawTranscriptFrameBytes
import BinWireRecordLengths
import ExtractedRowShape
import ExtractedRecordFraming
import BinWireParsedLengths
import R1PoseidonMap
import R1NoteHashMap
import R1AppendBindingMap
import R1SpendRelationMap
import R1SpendBaseDescent
import R1TraceSpendWitness
import R1ComputableTraceWitness

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1LiteralQueryRead, `R1LiteralRhoDensity, `R1LiteralByteSampler, `R1LiteralClassifier, `R1LiteralRun, `R1LiteralProtocol, `R1LiteralByteProtocol, `RawCutTranscriptRun, `RawCutProverCompiler, `RawCutWordsFromView, `BinCompiledRunWordStability, `RawSamplerSuffixCorrespondence, `BinThreeCommitmentTypedOpening, `BinSourceCommitmentWords, `BinWirePublicLengths, `ExtractedTerminalDecoderSuccess, `BinWireEnvelopeLengths, `BinWireBindingLengths, `RawTranscriptFrameBytes, `BinWireRecordLengths, `ExtractedRowShape, `ExtractedRecordFraming, `BinWireParsedLengths, `R1PoseidonMap, `R1NoteHashMap, `R1AppendBindingMap, `R1SpendRelationMap, `R1SpendBaseDescent, `R1TraceSpendWitness, `R1ComputableTraceWitness]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
