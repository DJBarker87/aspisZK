import Lean
import AspisFormal.V6PublishedTheoremInterfaces
import AspisFormal.Pool.AlgorithmicCircleDecoderV7
import AspisFormal.Pool.V7PairLeafOccupancy
import AspisFormal.V5FriBitReverse
import AspisFormal.V5FriExactLineDomains
import AspisFormal.V5FriInitialCircleEncoderIdentity
import AspisFormal.V5FriReleasedLineGeometry
import AspisFormal.V7ExactOneFoldDomains
import AspisR1AdapterReconstruct.Types
import AspisR1AdapterReconstruct.FunsExternal
import AspisR1AdapterReconstruct.Funs
import AspisR1BatchedFoldSourceStep
import AspisR1BatchedUsizeFlushBridgePublic
import AspisR1Qm31ArithmeticProbe.Types
import AspisR1Qm31ArithmeticProbe.Funs
import ExtractedCurrentReducerOps
import AspisV8R17.RawReducerNat
import ExtractedCurrentReducer
import AspisR1BatchedFoldArithmetic
import AspisR1BatchedWeightsExtraction.Types
import AspisR1BatchedWeightsExtraction.Funs
import AspisR1BatchedWeightsPushBodyStepV7
import ExtractedCurrentM31AddSub
import ExtractedCurrentTowerAdd
import ExtractedCurrentCM31Mul
import AspisR1PrefixAggregateParser.Types
import AspisR1PrefixAggregateParser.Funs
import AspisR1PublicPreparation.Types
import AspisR1PublicPreparation.Funs
import AspisR1Qm31SamplerIndex.Types

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`AspisFormal.V6PublishedTheoremInterfaces, `AspisFormal.Pool.AlgorithmicCircleDecoderV7, `AspisFormal.Pool.V7PairLeafOccupancy, `AspisFormal.V5FriBitReverse, `AspisFormal.V5FriExactLineDomains, `AspisFormal.V5FriInitialCircleEncoderIdentity, `AspisFormal.V5FriReleasedLineGeometry, `AspisFormal.V7ExactOneFoldDomains, `AspisR1AdapterReconstruct.Types, `AspisR1AdapterReconstruct.FunsExternal, `AspisR1AdapterReconstruct.Funs, `AspisR1BatchedFoldSourceStep, `AspisR1BatchedUsizeFlushBridgePublic, `AspisR1Qm31ArithmeticProbe.Types, `AspisR1Qm31ArithmeticProbe.Funs, `ExtractedCurrentReducerOps, `AspisV8R17.RawReducerNat, `ExtractedCurrentReducer, `AspisR1BatchedFoldArithmetic, `AspisR1BatchedWeightsExtraction.Types, `AspisR1BatchedWeightsExtraction.Funs, `AspisR1BatchedWeightsPushBodyStepV7, `ExtractedCurrentM31AddSub, `ExtractedCurrentTowerAdd, `ExtractedCurrentCM31Mul, `AspisR1PrefixAggregateParser.Types, `AspisR1PrefixAggregateParser.Funs, `AspisR1PublicPreparation.Types, `AspisR1PublicPreparation.Funs, `AspisR1Qm31SamplerIndex.Types]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
