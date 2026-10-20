import Lean
import CompPolySplitStateClosure
import CompPolyFactorAbortBound
import SequentialFreshProgram
import SequentialProgramInvariants
import CompPolySequentialFactorInvariant
import CompPolySequentialAbortBound
import CompPolySequentialRootsContract
import SequentialFiniteTapeLaw
import CompPolyFiniteRootSampler
import CompPolyGeneralRootsProgram
import CompPolyGeneralFiniteRootSampler
import CompPolyGeneralRootIndependentLaw
import ProgramQueryCost
import CompPolyGeneralRootQueryCost
import UnifiedDecoderCanonical
import PartialAddressImage
import LiteralDecoderEnrichment
import RawLiteralDecoderDensity
import RawAdaptiveLiteralDecoder
import LiteralBudgetEnvelope
import RawAdaptiveClassifierHitDensity
import DecodedFirstReadUnionBound
import DecodedFirstReadTraceBridge
import R1LiteralOpeningFunctionalFacts
import R1LiteralOpeningPrefixFacts
import R1LiteralSemanticIndex
import R1LiteralSemanticCodecBridge
import R1LiteralSemanticPayloadBridge
import R1LiteralSemanticPairs
import R1LiteralSemanticParserFacts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`CompPolySplitStateClosure, `CompPolyFactorAbortBound, `SequentialFreshProgram, `SequentialProgramInvariants, `CompPolySequentialFactorInvariant, `CompPolySequentialAbortBound, `CompPolySequentialRootsContract, `SequentialFiniteTapeLaw, `CompPolyFiniteRootSampler, `CompPolyGeneralRootsProgram, `CompPolyGeneralFiniteRootSampler, `CompPolyGeneralRootIndependentLaw, `ProgramQueryCost, `CompPolyGeneralRootQueryCost, `UnifiedDecoderCanonical, `PartialAddressImage, `LiteralDecoderEnrichment, `RawLiteralDecoderDensity, `RawAdaptiveLiteralDecoder, `LiteralBudgetEnvelope, `RawAdaptiveClassifierHitDensity, `DecodedFirstReadUnionBound, `DecodedFirstReadTraceBridge, `R1LiteralOpeningFunctionalFacts, `R1LiteralOpeningPrefixFacts, `R1LiteralSemanticIndex, `R1LiteralSemanticCodecBridge, `R1LiteralSemanticPayloadBridge, `R1LiteralSemanticPairs, `R1LiteralSemanticParserFacts]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
