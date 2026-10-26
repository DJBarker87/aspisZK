import Lean
import MultiproofConePhysicalNode
import MultiproofConePhysicalLogicalStep
import MultiproofConePhysicalPrelude
import MultiproofConePhysicalNodeForm
import MultiproofConePhysicalInputUnique
import MultiproofConePhysicalTrace
import MultiproofConePhysicalObservations
import MultiproofConePhysicalSourceLevel
import MultiproofConePhysicalFrozenLevels
import MultiproofConeRootGuard
import MultiproofConePhysicalVerify
import MultiproofConeCountGroups
import MultiproofConeCountLevels
import MultiproofConeCountPhysical
import MultiproofConeCountBounds
import MultiproofConeCountPhysicalLevels
import MultiproofConePadding
import MultiproofConeSlotTail
import MultiproofConeVerifyState
import MultiproofConeLeafFrozen
import MultiproofConeSlotState
import MultiproofConeBatches
import MultiproofConeFrozen2Stage
import MultiproofConeP6Composition
import MultiproofConeP6Verify
import MultiproofConeP6Batch
import MultiproofConeP6Callbacks
import MultiproofConeSlotAdapters
import MultiproofConeP6Frozen2Stage
import AspisR1Qm31ArithmeticProbe.Types
import AspisR1Qm31ArithmeticProbe.Funs
import ExtractedCurrentReducerOps
import S7Kani2AccumulatorLoop
import S7Kani2BasisLoop
import AspisV8R17.RawReducerNat
import ExtractedCurrentReducer
import S7Kani2PrefixLoop
import ExtractedCurrentM31AddSub
import S7Kani3BasisOuter
import S7Kani3BasisTotal
import S7JoinBasisBlock
import S7JoinBasisIdentity
import S7JoinBasisHighBit
import LineFold
import FoldRuntimeAlgebra
import FoldStoredGeometry
import FoldGeometryBridge
import S7OwnedP6StoredNode
import S7JoinBasisMachine
import S7JoinProductionBasis
import S7JoinBasisCanonical
import ExtractedCurrentTowerAdd
import ExtractedCurrentCM31Mul
import ExtractedCurrentQM31Mul
import AspisV8R17.QM31WordFormulas
import AspisV8R17.QM31WordResidues
import AspisV8R17.QuadraticTowerOperations
import AspisV8R17.QM31WordTower
import ExtractedCurrentQM31Tower
import ExtractedCurrentQM31Exact
import R22TotalCheckedComposition
import S7Kani2BackendArithmetic
import S7Kani3CanonicalBackend
import S7OwnedP6ScalarExtracted
import AspisR1BatchedFoldSourceStep
import S7OwnedP6ScalarProof
import S7Kani2OwnedRow
import S7Kani2OwnedRowRefinement
import S7JoinBackendCarriers
import S7Kani2OwnedPush
import S7Kani2OwnedPushModel
import S7Kani3PhaseInvariant
import AspisR1BatchedWeightsExtraction.Types
import AspisR1BatchedWeightsExtraction.Funs
import S8Kani2MutableSource
import S8Kani2MutableStep
import S8Kani2PendingWrite
import S8Kani2MutableLoop
import S8Kani2MutableOutput
import AspisR1BatchedUsizeFlushBridgePublic
import AspisR1BatchedActualCounter
import AspisR1BatchedFoldArithmetic
import AspisR1BatchedReducerBridge
import AspisR1BatchedActualReducerFinish
import AspisR1BatchedAllPrefix
import BatchedWeightsActualReducer
import AspisR1BatchedWeightsValueActualV12
import AspisR1BatchedWeightsValueActualV19
import S8Kani2MutableValue
import S8Kani2SliceSet
import S8Kani2PrefixIndex
import S8OwnedP6.Types
import S8OwnedP6.Funs
import S8OwnedP6ValueModel
import S7OwnedP6LoopSimulation
import S8OwnedP6LoopContracts
import S8OwnedP6Finish
import S8Kani2FinishTraversal
import S8Kani2ReferenceInduction
import S8OwnedP6R14Backend

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `MultiproofConePhysicalNode, `MultiproofConePhysicalLogicalStep, `MultiproofConePhysicalPrelude, `MultiproofConePhysicalNodeForm, `MultiproofConePhysicalInputUnique, `MultiproofConePhysicalTrace, `MultiproofConePhysicalObservations, `MultiproofConePhysicalSourceLevel, `MultiproofConePhysicalFrozenLevels, `MultiproofConeRootGuard, `MultiproofConePhysicalVerify, `MultiproofConeCountGroups, `MultiproofConeCountLevels, `MultiproofConeCountPhysical, `MultiproofConeCountBounds, `MultiproofConeCountPhysicalLevels, `MultiproofConePadding, `MultiproofConeSlotTail, `MultiproofConeVerifyState, `MultiproofConeLeafFrozen, `MultiproofConeSlotState, `MultiproofConeBatches, `MultiproofConeFrozen2Stage, `MultiproofConeP6Composition, `MultiproofConeP6Verify, `MultiproofConeP6Batch, `MultiproofConeP6Callbacks, `MultiproofConeSlotAdapters, `MultiproofConeP6Frozen2Stage, `AspisR1Qm31ArithmeticProbe.Types, `AspisR1Qm31ArithmeticProbe.Funs, `ExtractedCurrentReducerOps, `S7Kani2AccumulatorLoop, `S7Kani2BasisLoop, `AspisV8R17.RawReducerNat, `ExtractedCurrentReducer, `S7Kani2PrefixLoop, `ExtractedCurrentM31AddSub, `S7Kani3BasisOuter, `S7Kani3BasisTotal, `S7JoinBasisBlock, `S7JoinBasisIdentity, `S7JoinBasisHighBit, `LineFold, `FoldRuntimeAlgebra, `FoldStoredGeometry, `FoldGeometryBridge, `S7OwnedP6StoredNode, `S7JoinBasisMachine, `S7JoinProductionBasis, `S7JoinBasisCanonical, `ExtractedCurrentTowerAdd, `ExtractedCurrentCM31Mul, `ExtractedCurrentQM31Mul, `AspisV8R17.QM31WordFormulas, `AspisV8R17.QM31WordResidues, `AspisV8R17.QuadraticTowerOperations, `AspisV8R17.QM31WordTower, `ExtractedCurrentQM31Tower, `ExtractedCurrentQM31Exact, `R22TotalCheckedComposition, `S7Kani2BackendArithmetic, `S7Kani3CanonicalBackend, `S7OwnedP6ScalarExtracted, `AspisR1BatchedFoldSourceStep, `S7OwnedP6ScalarProof, `S7Kani2OwnedRow, `S7Kani2OwnedRowRefinement, `S7JoinBackendCarriers, `S7Kani2OwnedPush, `S7Kani2OwnedPushModel, `S7Kani3PhaseInvariant, `AspisR1BatchedWeightsExtraction.Types, `AspisR1BatchedWeightsExtraction.Funs, `S8Kani2MutableSource, `S8Kani2MutableStep, `S8Kani2PendingWrite, `S8Kani2MutableLoop, `S8Kani2MutableOutput, `AspisR1BatchedUsizeFlushBridgePublic, `AspisR1BatchedActualCounter, `AspisR1BatchedFoldArithmetic, `AspisR1BatchedReducerBridge, `AspisR1BatchedActualReducerFinish, `AspisR1BatchedAllPrefix, `BatchedWeightsActualReducer, `AspisR1BatchedWeightsValueActualV12, `AspisR1BatchedWeightsValueActualV19, `S8Kani2MutableValue, `S8Kani2SliceSet, `S8Kani2PrefixIndex, `S8OwnedP6.Types, `S8OwnedP6.Funs, `S8OwnedP6ValueModel, `S7OwnedP6LoopSimulation, `S8OwnedP6LoopContracts, `S8OwnedP6Finish, `S8Kani2FinishTraversal, `S8Kani2ReferenceInduction, `S8OwnedP6R14Backend ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ4_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ4_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ4_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ4_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ4_AUDIT_COMPLETE declarations={count} modules={selected.size}"
