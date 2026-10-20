import Lean
import R1LaterTableStability
import R1Line18Geometry
import R1RepeatedLift
import R1ParentSupport
import R1ConcreteProjection
import R1FinalResponses
import R1SecondFoldMatched
import R1SecondFoldRestoration
import R1FirstFoldRestoration
import R1JointList
import R1InitialResponses
import R1TwoFoldExtraction
import R1FunctionalBatchClean
import R1TwoRoundComparison
import R1TwoRoundPairing
import R1JointFunctionalBinding
import R1FunctionalWeights
import R1ConcreteBinding
import R1MatchingSupport
import R1CandidateDescent
import R1FixedWidthDecoder
import R1FixedWidthSlice
import R1FixedWidthEncoding
import R1ListFieldCodec
import R1RetainedExactLimbCodec
import R1ExactLeafFieldCodec
import R1MixedLeafEncoding
import R1MixedLeafSlices
import R1MixedLeafDecoder
import R1TypedRecoveredWords

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`R1LaterTableStability, `R1Line18Geometry, `R1RepeatedLift, `R1ParentSupport, `R1ConcreteProjection, `R1FinalResponses, `R1SecondFoldMatched, `R1SecondFoldRestoration, `R1FirstFoldRestoration, `R1JointList, `R1InitialResponses, `R1TwoFoldExtraction, `R1FunctionalBatchClean, `R1TwoRoundComparison, `R1TwoRoundPairing, `R1JointFunctionalBinding, `R1FunctionalWeights, `R1ConcreteBinding, `R1MatchingSupport, `R1CandidateDescent, `R1FixedWidthDecoder, `R1FixedWidthSlice, `R1FixedWidthEncoding, `R1ListFieldCodec, `R1RetainedExactLimbCodec, `R1ExactLeafFieldCodec, `R1MixedLeafEncoding, `R1MixedLeafSlices, `R1MixedLeafDecoder, `R1TypedRecoveredWords]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
