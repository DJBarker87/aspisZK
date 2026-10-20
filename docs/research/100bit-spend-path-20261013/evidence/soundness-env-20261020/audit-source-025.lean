import Lean
import RawBoundedTrace
import RawBackgroundCompletion
import RawUnifiedDecoder
import R1SemanticBudget
import R1PerAttemptEnvelope
import HchecksAccumulator
import R1TypedPrefixParser
import R1SemanticPrefixCodec
import R1GenericNoHitIndex
import R1LiteralOpeningDataRows
import R1LiteralSpendExtraction
import R0P.MaskSemantics
import R1MaskedSemantic
import R1SemanticCandidateList
import R0P.MaskPrefix
import R0P.MaskNoHit
import R1SemanticHit
import R0P.MaskEarly
import R1SemanticPrefix
import R1LiteralSemanticTerminalBridge
import R1SelectedOpeningPairing
import ExtractedAdapterReconstructSuccess
import ExtractedAdapterTransferBindings
import PublicRawCore
import PublicRawAmountGuard
import R1PublicSourceRaw
import R1PublicByteCodec
import R1PublicByteCodecLaws
import R1PublicCodecAgreement
import R1PublicSourceRawMap

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`RawBoundedTrace, `RawBackgroundCompletion, `RawUnifiedDecoder, `R1SemanticBudget, `R1PerAttemptEnvelope, `HchecksAccumulator, `R1TypedPrefixParser, `R1SemanticPrefixCodec, `R1GenericNoHitIndex, `R1LiteralOpeningDataRows, `R1LiteralSpendExtraction, `R0P.MaskSemantics, `R1MaskedSemantic, `R1SemanticCandidateList, `R0P.MaskPrefix, `R0P.MaskNoHit, `R1SemanticHit, `R0P.MaskEarly, `R1SemanticPrefix, `R1LiteralSemanticTerminalBridge, `R1SelectedOpeningPairing, `ExtractedAdapterReconstructSuccess, `ExtractedAdapterTransferBindings, `PublicRawCore, `PublicRawAmountGuard, `R1PublicSourceRaw, `R1PublicByteCodec, `R1PublicByteCodecLaws, `R1PublicCodecAgreement, `R1PublicSourceRawMap]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
