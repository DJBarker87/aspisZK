import Lean
import ActualRawPowCoefficientBudget
import ActualRawLongDivisionCost
import ActualRawModRemainderCostBridge
import ActualCompPolyGCDCostMirror
import ActualRawModRemainderSizeBound
import CompPolyModularRemainderDegree
import ActualModularProductDegreeBound
import ActualRawModRemainderDegreeBridge
import ActualRawLongDivisionCostV4
import RawMulSizeBoundV5
import ActualDivisionStepCostBoundV9
import PrivateDivStepBridgeV2
import ActualLongDivisionTotalCostV2
import ActualScaledDivisorMonic
import ActualRawModCostBound
import ActualCompPolyGCDTotalRemainderCost
import ActualCompPolyPowCost
import AspisR1BatchedActualCounter
import AspisR1BatchedReducerBridge
import AspisR1BatchedActualReducerFinish
import AspisR1BatchedAllPrefix
import AspisR1BatchedWeightsPushBodyBoundedV4
import AspisR1BatchedWeightsPushBodyBoundedV5
import AspisR1BatchedWeightsPushBodyBoundedV6
import AspisR1BatchedWeightsPushBodyValueStepV1
import AspisR1BatchedWeightsPushBodyValueStepV2
import AspisR1BatchedWeightsPushBodyValueStepV3
import AspisR1BatchedWeightsSetCellFactsV1
import AspisR1PublicSerializer.Types
import AspisR1PublicSerializer.Funs

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owners : List Name := [`ActualRawPowCoefficientBudget, `ActualRawLongDivisionCost, `ActualRawModRemainderCostBridge, `ActualCompPolyGCDCostMirror, `ActualRawModRemainderSizeBound, `CompPolyModularRemainderDegree, `ActualModularProductDegreeBound, `ActualRawModRemainderDegreeBridge, `ActualRawLongDivisionCostV4, `RawMulSizeBoundV5, `ActualDivisionStepCostBoundV9, `PrivateDivStepBridgeV2, `ActualLongDivisionTotalCostV2, `ActualScaledDivisorMonic, `ActualRawModCostBound, `ActualCompPolyGCDTotalRemainderCost, `ActualCompPolyPowCost, `AspisR1BatchedActualCounter, `AspisR1BatchedReducerBridge, `AspisR1BatchedActualReducerFinish, `AspisR1BatchedAllPrefix, `AspisR1BatchedWeightsPushBodyBoundedV4, `AspisR1BatchedWeightsPushBodyBoundedV5, `AspisR1BatchedWeightsPushBodyBoundedV6, `AspisR1BatchedWeightsPushBodyValueStepV1, `AspisR1BatchedWeightsPushBodyValueStepV2, `AspisR1BatchedWeightsPushBodyValueStepV3, `AspisR1BatchedWeightsSetCellFactsV1, `AspisR1PublicSerializer.Types, `AspisR1PublicSerializer.Funs]
  for entry in env.constants.toList do
    let decl := entry.1
    if let some idx := env.getModuleIdxFor? decl then
      let owner := env.header.moduleNames[idx]!
      if owners.contains owner then
        let axs ← collectAxioms decl
        logInfo m!"S_AXIOMS {owner} | {decl} | {axs.toList}"
