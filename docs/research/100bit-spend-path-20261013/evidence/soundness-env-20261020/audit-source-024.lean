import Lean
import ExtractedSourceFull25Frames
import ExtractedSourceDigestAddresses
import RawSourceDigestLog
import ExtractedSourceSemanticSampler
import ExtractedSourceDigestOracle
import RawSamplerSuffixSourceFrames
import Stage2ContinuationTypes
import WireTx2BinaryBodies
import WireTx2Records
import WireTx2SliceFacts
import WireTx2LeafBodies
import WireTx2LeafCalls
import BinWirePublicLengths
import ExtractedTerminalDecoderSuccess
import BinWireEnvelopeLengths
import R1PoseidonMap
import R1NoteHashMap
import R1AppendBindingMap
import R1SpendRelationMap
import R1SpendBaseDescent
import R1TraceSpendWitness
import R1CandidateBaseProjection
import R1InputWitness
import R1AppendSemantics
import R1SpendRelationExtraction
import R1ConcreteSpendExtraction
import R1CanonicalAddressEmbedding
import CanonicalRawTrace
import UnifiedDecoderCanonical
import PartialAddressImage

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`ExtractedSourceFull25Frames, `ExtractedSourceDigestAddresses, `RawSourceDigestLog, `ExtractedSourceSemanticSampler, `ExtractedSourceDigestOracle, `RawSamplerSuffixSourceFrames, `Stage2ContinuationTypes, `WireTx2BinaryBodies, `WireTx2Records, `WireTx2SliceFacts, `WireTx2LeafBodies, `WireTx2LeafCalls, `BinWirePublicLengths, `ExtractedTerminalDecoderSuccess, `BinWireEnvelopeLengths, `R1PoseidonMap, `R1NoteHashMap, `R1AppendBindingMap, `R1SpendRelationMap, `R1SpendBaseDescent, `R1TraceSpendWitness, `R1CandidateBaseProjection, `R1InputWitness, `R1AppendSemantics, `R1SpendRelationExtraction, `R1ConcreteSpendExtraction, `R1CanonicalAddressEmbedding, `CanonicalRawTrace, `UnifiedDecoderCanonical, `PartialAddressImage]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
