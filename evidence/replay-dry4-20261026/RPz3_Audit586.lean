import Lean
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
import S7OwnedP6LoopSimulation
import S8OwnedP6LoopContracts
import R1CandidateFieldParsers
import S7OwnedP6RowContract
import S2TrustedSdkBorrow
import S2W_TrustedStd
import AdapterRwRuntimeAdmission
import AdapterRwSdkSnapshots
import S2W_WrapperLaws
import MultiproofConeBool
import MultiproofConeRead16
import MultiproofConeVecLaws
import MultiproofConePush
import AspisR1Qm31SamplerIndex.Types
import AspisR1Qm31SamplerIndex.Funs
import R1SamplerLongDivision
import R1SamplerMachineBounds
import R1SamplerWord
import R1SamplerPass
import R1SamplerWordPass
import ExtractedQM31SamplerPass
import ExtractedQM31SamplerPassLoop
import ExtractedQM31SamplerDivision
import ExtractedQM31SamplerBytes
import R1SamplerAddDigits
import R1SamplerCarry
import R1SamplerDigits
import R1SamplerArithmetic
import R1SamplerAddBridge
import R1SamplerRanking
import R1SamplerNatModel
import R1SamplerRepeatedPass
import ExtractedQM31SamplerDigits
import ExtractedCurrentQM31Equality
import ExtractedQM31SamplerCarrier
import R1SamplerBlockRank
import AspisR1DecodeKFullV10.Types
import DecodeKOptionDiscriminantBridge
import AspisR1DecodeKFullV10.Funs
import AspisR1DecodeKFullV10ParserCanonicality
import AspisR1DecodeKFullParserCanonicalityCMQ
import AspisR1DecodeKFullHelperCanonicality
import AspisR1DecodeKCanonicalArrayInvariant
import AspisR1DecodeKFullLoopBodyFrame
import OccupancyRangeTraversal
import AspisR1DecodeKFullLoopFuelCanonicality
import AspisR1DecodeKFullLoopBodyPendingFrame
import AspisR1DecodeKFullLoopPendingFuel
import AspisR1DecodeKFullSuccessCanonicality
import CurrentCompactCallerTypesV1
import CurrentCompactCallerModelV1
import CurrentCompactPrepareReachabilityV1
import CurrentCompactTx1ReachabilityV1
import AspisR1WithdrawalCaller.Types
import AspisR1WithdrawalCaller.Funs
import ExtractedWithdrawalCallerSuccess
import AspisR1TerminalDecoder.Types
import AspisR1TerminalDecoder.FunsExternal
import AspisR1TerminalDecoder.Funs
import ExtractedTerminalDecoderSuccess
import ExtractedDecoderWithdrawalSuccess
import ExtractedDecoderCallerBridge
import ExtractedWithdrawalCallerCarrier
import ExtractedWithdrawalCallerPublic
import ExtractedDecoderPublicBridge
import ExtractedDecoderPublicBinding
import AspisR1PrefixAggregateParser.Types

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `ExtractedCurrentQM31Tower, `ExtractedCurrentQM31Exact, `R22TotalCheckedComposition, `S7Kani2BackendArithmetic, `S7Kani3CanonicalBackend, `S7OwnedP6ScalarExtracted, `AspisR1BatchedFoldSourceStep, `S7OwnedP6ScalarProof, `S7Kani2OwnedRow, `S7Kani2OwnedRowRefinement, `S7JoinBackendCarriers, `S7Kani2OwnedPush, `S7Kani2OwnedPushModel, `S7Kani3PhaseInvariant, `AspisR1BatchedWeightsExtraction.Types, `AspisR1BatchedWeightsExtraction.Funs, `S8Kani2MutableSource, `S8Kani2MutableStep, `S8Kani2PendingWrite, `S8Kani2MutableLoop, `S8Kani2MutableOutput, `AspisR1BatchedUsizeFlushBridgePublic, `AspisR1BatchedActualCounter, `AspisR1BatchedFoldArithmetic, `AspisR1BatchedReducerBridge, `AspisR1BatchedActualReducerFinish, `AspisR1BatchedAllPrefix, `BatchedWeightsActualReducer, `AspisR1BatchedWeightsValueActualV12, `AspisR1BatchedWeightsValueActualV19, `S8Kani2MutableValue, `S8Kani2SliceSet, `S8Kani2PrefixIndex, `S7OwnedP6LoopSimulation, `S8OwnedP6LoopContracts, `R1CandidateFieldParsers, `S7OwnedP6RowContract, `S2TrustedSdkBorrow, `S2W_TrustedStd, `AdapterRwRuntimeAdmission, `AdapterRwSdkSnapshots, `S2W_WrapperLaws, `MultiproofConeBool, `MultiproofConeRead16, `MultiproofConeVecLaws, `MultiproofConePush, `AspisR1Qm31SamplerIndex.Types, `AspisR1Qm31SamplerIndex.Funs, `R1SamplerLongDivision, `R1SamplerMachineBounds, `R1SamplerWord, `R1SamplerPass, `R1SamplerWordPass, `ExtractedQM31SamplerPass, `ExtractedQM31SamplerPassLoop, `ExtractedQM31SamplerDivision, `ExtractedQM31SamplerBytes, `R1SamplerAddDigits, `R1SamplerCarry, `R1SamplerDigits, `R1SamplerArithmetic, `R1SamplerAddBridge, `R1SamplerRanking, `R1SamplerNatModel, `R1SamplerRepeatedPass, `ExtractedQM31SamplerDigits, `ExtractedCurrentQM31Equality, `ExtractedQM31SamplerCarrier, `R1SamplerBlockRank, `AspisR1DecodeKFullV10.Types, `DecodeKOptionDiscriminantBridge, `AspisR1DecodeKFullV10.Funs, `AspisR1DecodeKFullV10ParserCanonicality, `AspisR1DecodeKFullParserCanonicalityCMQ, `AspisR1DecodeKFullHelperCanonicality, `AspisR1DecodeKCanonicalArrayInvariant, `AspisR1DecodeKFullLoopBodyFrame, `OccupancyRangeTraversal, `AspisR1DecodeKFullLoopFuelCanonicality, `AspisR1DecodeKFullLoopBodyPendingFrame, `AspisR1DecodeKFullLoopPendingFuel, `AspisR1DecodeKFullSuccessCanonicality, `CurrentCompactCallerTypesV1, `CurrentCompactCallerModelV1, `CurrentCompactPrepareReachabilityV1, `CurrentCompactTx1ReachabilityV1, `AspisR1WithdrawalCaller.Types, `AspisR1WithdrawalCaller.Funs, `ExtractedWithdrawalCallerSuccess, `AspisR1TerminalDecoder.Types, `AspisR1TerminalDecoder.FunsExternal, `AspisR1TerminalDecoder.Funs, `ExtractedTerminalDecoderSuccess, `ExtractedDecoderWithdrawalSuccess, `ExtractedDecoderCallerBridge, `ExtractedWithdrawalCallerCarrier, `ExtractedWithdrawalCallerPublic, `ExtractedDecoderPublicBridge, `ExtractedDecoderPublicBinding, `AspisR1PrefixAggregateParser.Types ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ3_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ3_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner && n.hash.toNat % 1 == 0 then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ3_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ3_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ3_AUDIT_COMPLETE declarations={count} modules={selected.size}"
