import Lean
import R0P.SemD2Glue
import R0P.MaskD2
import R0P.MaskBadSets
import R0P.MaskDensity
import R0P.SemDuplexDecoder
import R0P.MaskDuplexDecoder
import R0P.MaskSource
import R0P.MaskD2Glue
import R1OpeningSamplerBound
import R1SelectedSamplerRanks
import R1SelectedChallengeMap
import R1RawFunctionalWeights
import R1RawPairing
import R1RawOpening
import R1D18PointWeights
import R1D18OpeningWeights
import R1SemanticOpening
import R1SemanticTransport
import R1SelectedCircleWeightModel
import R1SelectedOpeningFunctionals
import R1SelectedSemanticMessages
import R1SelectedFieldSequenceCodec
import R1CircleRecordCodec
import R1LengthFrameCodec
import R1OpeningRecordCodec
import R1SelectedIndexedRead
import R1SelectedPrefixRead
import R1SelectedOpeningStages
import R1SelectedOpeningClaims
import R1OpeningPolynomialView

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R0P.SemD2Glue, `R0P.MaskD2, `R0P.MaskBadSets, `R0P.MaskDensity, `R0P.SemDuplexDecoder, `R0P.MaskDuplexDecoder, `R0P.MaskSource, `R0P.MaskD2Glue, `R1OpeningSamplerBound, `R1SelectedSamplerRanks, `R1SelectedChallengeMap, `R1RawFunctionalWeights, `R1RawPairing, `R1RawOpening, `R1D18PointWeights, `R1D18OpeningWeights, `R1SemanticOpening, `R1SemanticTransport, `R1SelectedCircleWeightModel, `R1SelectedOpeningFunctionals, `R1SelectedSemanticMessages, `R1SelectedFieldSequenceCodec, `R1CircleRecordCodec, `R1LengthFrameCodec, `R1OpeningRecordCodec, `R1SelectedIndexedRead, `R1SelectedPrefixRead, `R1SelectedOpeningStages, `R1SelectedOpeningClaims, `R1OpeningPolynomialView]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
