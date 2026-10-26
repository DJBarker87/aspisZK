import Lean
import R17NarrowFunsB11ChunkPower
import R17ActualB11IndexPower
import R17TableBChunk12Certificate
import R17NarrowFunsB12ChunkPower
import R17ActualB12IndexPower
import R17TableBChunk13Certificate
import R17NarrowFunsB13ChunkPower
import R17ActualB13IndexPower
import R17TableBChunk14Certificate
import R17NarrowFunsB14ChunkPower
import R17ActualB14IndexPower
import R17TableBChunk15Certificate
import R17NarrowFunsB15ChunkPower
import R17ActualB15IndexPower
import R17ZPowAddition
import R17ActualWholeTablePower
import R17CircleCoordinateMulBridge
import R17CircleCoordinatePowerBridge
import R17TableCirclePowerBridge
import R17FibrePointStoredDomain
import R17FibrePointActualSuccess
import R1ZCircleFoldMathV1
import R1ZQueryGeometryValuesV6
import R17FibrePointLineNode
import R17FibrePointLineNodeActual
import R17CurrentM31Semantics
import CurrentWideBaseBridge
import CurrentWideQMBridge
import CurrentWideQMField
import CurrentWideField
import CurrentWideMulSourceGraph
import CurrentWideMulExact
import CurrentWideMulExactProduct
import CurrentPowersExactProduct
import LoopPowersCandidateModel
import LoopPowersCandidateSteps
import LoopPowersCandidatePrefix
import LoopPowersCandidateTotal
import LoopPowersZeroCandidate
import LoopPowersEarlySteps
import LoopPowersEarlyTotal
import R17CurrentCM31Semantics
import R17CurrentDomainSource
import R17CurrentDomainCanonical
import CurrentWideMulU
import CurrentWideQMSubV5
import CurrentWideProduct
import CurrentWideQMMulM31V5
import CurrentWideMulM31V13
import CurrentWideEqSemanticV7
import WeightsFieldExplicitDecoder
import WeightsFieldSuccess
import AspisR1RecordParser.Types
import AspisR1RecordParser.Funs
import ExtractedRecordLimbCanonicality
import ExtractedRecordByteCanonicality
import CurrentCallerUsizeArithmeticV1
import SelectedWideViewTypesV1
import R1CandidateWideParserSource
import UnrolledWideParserSource
import R1UnrolledWideLimbChecks
import CurrentWideCanonicalInjectivityV1
import StatefulArrayFromFnModelV1
import CurrentPowersCallbackInvariant
import S3PowersCanonicalTraceV1
import PowersP6IndexedOutputV1
import S4FromFnP6GeneratedTrace
import S4FromFnP6GeneratedInterface
import EbyKPushExplicitTypesV1
import AspisR1EbyKPushExplicitOpsV1
import AspisR1EbyKCheckedQAllParamV1
import EbyKCheckedQConcreteAll
import EbyKCheckedQCanonicality
import AspisR1EbyKPushWideToQ
import AspisR1EbyKPushSourceConversionV1
import AspisR1EbyKPushConcreteCheckedQV1
import EbyKPushCheckedScalarCanonical
import AspisR1DotPushLocal.Types
import AspisR1DotPushLocal.Funs
import EbyKDotPushNatStep
import CheckedWrappingScalarAgreement
import EbyKDotPushCanonicalFoldBridgeV1
import EbyKDotPushActualFoldV2
import DotPushWordSource
import DotPushFourCoordinates
import DotPushSourceResidues
import DotPushSuccessResidues
import EbyKPushDotBackend
import AspisR1EbyKFinish.Types
import SelectorArrayMapRuntimeSlice
import AspisR1EbyKFinish.Funs
import SelectorArrayMapSuccess
import EbyKPowerValueCanonicalToPushV5
import AspisR1GammaCaller.Types
import GammaCallerExplicitHelpers
import AspisR1Post25Sampler.Types
import AspisR1Post25Sampler.Funs
import AspisR1Post25SamplerIndexedAddSmallCandidate.Types
import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs
import IndexedCandidateAddSmallGeneratedOneStepV1

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R17NarrowFunsB11ChunkPower, `R17ActualB11IndexPower, `R17TableBChunk12Certificate, `R17NarrowFunsB12ChunkPower, `R17ActualB12IndexPower, `R17TableBChunk13Certificate, `R17NarrowFunsB13ChunkPower, `R17ActualB13IndexPower, `R17TableBChunk14Certificate, `R17NarrowFunsB14ChunkPower, `R17ActualB14IndexPower, `R17TableBChunk15Certificate, `R17NarrowFunsB15ChunkPower, `R17ActualB15IndexPower, `R17ZPowAddition, `R17ActualWholeTablePower, `R17CircleCoordinateMulBridge, `R17CircleCoordinatePowerBridge, `R17TableCirclePowerBridge, `R17FibrePointStoredDomain, `R17FibrePointActualSuccess, `R1ZCircleFoldMathV1, `R1ZQueryGeometryValuesV6, `R17FibrePointLineNode, `R17FibrePointLineNodeActual, `R17CurrentM31Semantics, `CurrentWideBaseBridge, `CurrentWideQMBridge, `CurrentWideQMField, `CurrentWideField, `CurrentWideMulSourceGraph, `CurrentWideMulExact, `CurrentWideMulExactProduct, `CurrentPowersExactProduct, `LoopPowersCandidateModel, `LoopPowersCandidateSteps, `LoopPowersCandidatePrefix, `LoopPowersCandidateTotal, `LoopPowersZeroCandidate, `LoopPowersEarlySteps, `LoopPowersEarlyTotal, `R17CurrentCM31Semantics, `R17CurrentDomainSource, `R17CurrentDomainCanonical, `CurrentWideMulU, `CurrentWideQMSubV5, `CurrentWideProduct, `CurrentWideQMMulM31V5, `CurrentWideMulM31V13, `CurrentWideEqSemanticV7, `WeightsFieldExplicitDecoder, `WeightsFieldSuccess, `AspisR1RecordParser.Types, `AspisR1RecordParser.Funs, `ExtractedRecordLimbCanonicality, `ExtractedRecordByteCanonicality, `CurrentCallerUsizeArithmeticV1, `SelectedWideViewTypesV1, `R1CandidateWideParserSource, `UnrolledWideParserSource, `R1UnrolledWideLimbChecks, `CurrentWideCanonicalInjectivityV1, `StatefulArrayFromFnModelV1, `CurrentPowersCallbackInvariant, `S3PowersCanonicalTraceV1, `PowersP6IndexedOutputV1, `S4FromFnP6GeneratedTrace, `S4FromFnP6GeneratedInterface, `EbyKPushExplicitTypesV1, `AspisR1EbyKPushExplicitOpsV1, `AspisR1EbyKCheckedQAllParamV1, `EbyKCheckedQConcreteAll, `EbyKCheckedQCanonicality, `AspisR1EbyKPushWideToQ, `AspisR1EbyKPushSourceConversionV1, `AspisR1EbyKPushConcreteCheckedQV1, `EbyKPushCheckedScalarCanonical, `AspisR1DotPushLocal.Types, `AspisR1DotPushLocal.Funs, `EbyKDotPushNatStep, `CheckedWrappingScalarAgreement, `EbyKDotPushCanonicalFoldBridgeV1, `EbyKDotPushActualFoldV2, `DotPushWordSource, `DotPushFourCoordinates, `DotPushSourceResidues, `DotPushSuccessResidues, `EbyKPushDotBackend, `AspisR1EbyKFinish.Types, `SelectorArrayMapRuntimeSlice, `AspisR1EbyKFinish.Funs, `SelectorArrayMapSuccess, `EbyKPowerValueCanonicalToPushV5, `AspisR1GammaCaller.Types, `GammaCallerExplicitHelpers, `AspisR1Post25Sampler.Types, `AspisR1Post25Sampler.Funs, `AspisR1Post25SamplerIndexedAddSmallCandidate.Types, `AspisR1Post25SamplerIndexedAddSmallCandidate.Funs, `IndexedCandidateAddSmallGeneratedOneStepV1 ]
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
