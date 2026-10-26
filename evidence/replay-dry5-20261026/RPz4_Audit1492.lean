import Lean
import R1ZCircleFoldMathV1
import R1ZQueryGeometryValuesV6
import R17FibrePointLineNode
import R17FibrePointLineNodeActual
import R17CurrentM31Semantics
import CurrentWideBaseBridge
import CurrentWideQMBridge
import CurrentWideQMField
import CurrentWideField
import CurrentWideMulCanonical
import CurrentWideMulSourceGraph
import CurrentWideMulExact
import CurrentWideMulExactProduct
import CurrentWideLinearExact
import CurrentClaimSumModel
import CurrentClaimSumSteps
import CurrentClaimSumTotal
import CurrentClaimDotModel
import CurrentPowersCallback
import CurrentPowersConcreteMul
import CurrentPowersExactProduct
import LoopPowersCandidateModel
import LoopPowersCandidateSteps
import LoopPowersCandidatePrefix
import LoopPowersCandidateTotal
import LoopPowersZeroCandidate
import LoopPowersEarlySteps
import LoopPowersEarlyTotal
import CurrentClaimPowersInstance
import CurrentClaimOuterBody
import CurrentClaimRangeStep
import CurrentClaimOuterTrace
import CurrentClaimCallerComposition
import R17CurrentCM31Semantics
import R17CurrentDomainSource
import R17CurrentDomainCanonical
import CurrentWideMulU
import CurrentWideQMSubV5
import CurrentWideProduct
import CurrentWideQMMulM31V5
import CurrentWideMulM31V13
import AspisR1FinishRelationCurrent.Types
import FinishCandidateExplicitOps
import FinishCandidateRoundSuccess
import FinishCandidateOuterSuccess
import FinishCandidateEquations
import CurrentFinishArithmetic
import CurrentWideEqSemanticV7
import CurrentFinishEquality
import WeightsFieldExplicitDecoder
import WeightsFieldSuccess
import AspisR1RecordParser.Types
import AspisR1RecordParser.Funs
import ExtractedRecordLimbCanonicality
import ExtractedRecordByteCanonicality
import FinishFieldSelectorAdapterV2
import CurrentFinishField
import CurrentClaimParserInstance
import CurrentClaimScalarNormalForm
import CurrentClaimScalarBody
import CurrentClaimScalarChain
import S1ClaimDotBoundedResultV1
import S1ClaimBoundedResultCompositionV1
import S1ClaimAllLoopsBoundedV1
import S1ClaimOwnedNestedModelV1
import S1ClaimOwnedNestedTransferV1
import S1ClaimOwnedNestedLoopsV1
import S1ClaimOwnedInnerCompleteV1
import S1ClaimOwnedInnerCpsV1
import S1ClaimOwnedOuterStepV1
import S1ClaimOwnedOuterCompleteV1
import S1ClaimSliceCarrierV1
import S1ClaimBorrowedAbiNativeV1
import S1ClaimBorrowedAbiTransportV1
import CurrentCallerUsizeArithmeticV1
import CurrentCompactCallerConstantsV1
import SelectedWideViewTypesV1
import R1CandidateWideParserSource
import UnrolledWideParserSource
import R1CandidateFieldCanonicality
import R1WideParserArrayHalves
import R1CandidateWideParserRefinement
import UnrolledWideByteReads
import R1UnrolledWideLimbChecks
import R1CandidateWideParserContracts
import UnrolledWideParserRefinement
import SelectedWideViewFunsV1
import CurrentWideCanonicalInjectivityV1
import StatefulArrayFromFnModelV1
import CurrentPowersCallbackInvariant
import S3PowersCanonicalTraceV1
import PowersP6IndexedOutputV1
import PowersP6ClaimAgreementV1
import S4FromFnP6GeneratedTrace
import S4FromFnP6GeneratedInterface
import PowersP6GeneratedErasureV1
import PowersP6GeneratedTotalV1
import CurrentClaimPartsUpdates
import CurrentClaimFinalParts
import CurrentClaimOuterSum

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `R1ZCircleFoldMathV1, `R1ZQueryGeometryValuesV6, `R17FibrePointLineNode, `R17FibrePointLineNodeActual, `R17CurrentM31Semantics, `CurrentWideBaseBridge, `CurrentWideQMBridge, `CurrentWideQMField, `CurrentWideField, `CurrentWideMulCanonical, `CurrentWideMulSourceGraph, `CurrentWideMulExact, `CurrentWideMulExactProduct, `CurrentWideLinearExact, `CurrentClaimSumModel, `CurrentClaimSumSteps, `CurrentClaimSumTotal, `CurrentClaimDotModel, `CurrentPowersCallback, `CurrentPowersConcreteMul, `CurrentPowersExactProduct, `LoopPowersCandidateModel, `LoopPowersCandidateSteps, `LoopPowersCandidatePrefix, `LoopPowersCandidateTotal, `LoopPowersZeroCandidate, `LoopPowersEarlySteps, `LoopPowersEarlyTotal, `CurrentClaimPowersInstance, `CurrentClaimOuterBody, `CurrentClaimRangeStep, `CurrentClaimOuterTrace, `CurrentClaimCallerComposition, `R17CurrentCM31Semantics, `R17CurrentDomainSource, `R17CurrentDomainCanonical, `CurrentWideMulU, `CurrentWideQMSubV5, `CurrentWideProduct, `CurrentWideQMMulM31V5, `CurrentWideMulM31V13, `AspisR1FinishRelationCurrent.Types, `FinishCandidateExplicitOps, `FinishCandidateRoundSuccess, `FinishCandidateOuterSuccess, `FinishCandidateEquations, `CurrentFinishArithmetic, `CurrentWideEqSemanticV7, `CurrentFinishEquality, `WeightsFieldExplicitDecoder, `WeightsFieldSuccess, `AspisR1RecordParser.Types, `AspisR1RecordParser.Funs, `ExtractedRecordLimbCanonicality, `ExtractedRecordByteCanonicality, `FinishFieldSelectorAdapterV2, `CurrentFinishField, `CurrentClaimParserInstance, `CurrentClaimScalarNormalForm, `CurrentClaimScalarBody, `CurrentClaimScalarChain, `S1ClaimDotBoundedResultV1, `S1ClaimBoundedResultCompositionV1, `S1ClaimAllLoopsBoundedV1, `S1ClaimOwnedNestedModelV1, `S1ClaimOwnedNestedTransferV1, `S1ClaimOwnedNestedLoopsV1, `S1ClaimOwnedInnerCompleteV1, `S1ClaimOwnedInnerCpsV1, `S1ClaimOwnedOuterStepV1, `S1ClaimOwnedOuterCompleteV1, `S1ClaimSliceCarrierV1, `S1ClaimBorrowedAbiNativeV1, `S1ClaimBorrowedAbiTransportV1, `CurrentCallerUsizeArithmeticV1, `CurrentCompactCallerConstantsV1, `SelectedWideViewTypesV1, `R1CandidateWideParserSource, `UnrolledWideParserSource, `R1CandidateFieldCanonicality, `R1WideParserArrayHalves, `R1CandidateWideParserRefinement, `UnrolledWideByteReads, `R1UnrolledWideLimbChecks, `R1CandidateWideParserContracts, `UnrolledWideParserRefinement, `SelectedWideViewFunsV1, `CurrentWideCanonicalInjectivityV1, `StatefulArrayFromFnModelV1, `CurrentPowersCallbackInvariant, `S3PowersCanonicalTraceV1, `PowersP6IndexedOutputV1, `PowersP6ClaimAgreementV1, `S4FromFnP6GeneratedTrace, `S4FromFnP6GeneratedInterface, `PowersP6GeneratedErasureV1, `PowersP6GeneratedTotalV1, `CurrentClaimPartsUpdates, `CurrentClaimFinalParts, `CurrentClaimOuterSum ]
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
