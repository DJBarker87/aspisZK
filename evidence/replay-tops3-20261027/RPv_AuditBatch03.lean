import Lean
import RPv_FIx_HighSumOuter
import RPv_FIx_HighSum
import RPv_FIx_ScheduleModel
import RPv_FIx_ScheduleIndices
import RPv_FIx_InitialWrites
import RPv_FIv_PreparedMul
import RPv_FIx_InitialArray
import RPv_FIx_AbsorptionArray
import RPv_FIx_ScheduleValue
import RPv_FIx_SchedulePacked
import RPv_FIx_PathLiteral
import RPv_FIx_PathModel
import RPv_FIx_PathMeaning
import RPv_FIx_PathPacked
import RPv_FIy_CoefficientSource
import RPv_FIy_IteratorShape
import RPv_FIy_ListDecoded
import RPv_FIy_ScalarPacked
import RPv_FIy_NativeCoefficients
import RPv_FIw_CompositionOrigins
import RPv_FIr_NativeArithmetic
import RPv_FIr_NativeCM
import RPv_FIr_NativeQM
import RPv_FIr_NativeValue
import RPv_FIr_NativeArray
import RPv_FIr_ArrayRead
import RPv_FIr_BuilderCanonical
import RPv_FIr_SelectedClaim
import RPv_FIw_OpeningCanonical
import RPv_FIy_PartialRoot
import RPv_FIy_ScalingSource
import RPv_FIy_ScalingNonvacuity
import RPv_F3X_FixtureRuntime
import RPv_F3X_FixtureSource
import RPv_Rc10_Nonvacuity
import RPv_FIq_Top
import RPv_FIr_Top
import RPv_FIp_Nonvacuity
import RPv_FIq_Nonvacuity
import RPv_FIr_Nonvacuity
import RPv_FIy_Statements
import RPv_FIw_PublicModel
import RPv_FIy_ValueRangeShape
import RPv_FIy_ValueRangeList
import RPv_FIy_ValueFamilyList
import RPv_FIy_Audit
import RPv_FIz_BoxedOrigins
import RPv_FIz_Marginals
import RPv_FIz_RangeFold
import RPv_FIz_RangeMarginal
import RPv_FIz_ScheduleNodes
import RPv_FIz_InitialShape
import RPv_FIz_ScheduleShape
import RPv_FIz_ScheduleInitial
import RPv_FIz_ScheduleAbsorption
import RPv_FIz_ScheduleFamily
import RPv_FIz_PathList
import RPv_FIz_PathSelector
import RPv_FIz_PathFamily
import RPv_FIz_OccupancyFamily
import RPv_FIz_DigestRead
import RPv_FIz_DigestBinding
import RPv_FIz_DigestPrefix
import RPv_FIz_EmptyRoots
import RPv_FIz_EmptyBound
import RPv_FIz_EmptyRight
import RPv_FIz_DigestFrontier
import RPv_FIz_DigestFold
import RPv_FIz_DigestSuffix
import RPv_FIz_PublicDigest
import RPv_FIz_DigestFamily
import RPv_FIz_ScalarFamily
import RPv_FIz_ScalarList
import RPv_FIz_SelectedList
import RPv_FIz_ContributionList
import RPv_FIz_PackLinear
import RPv_FIz_ContributionAppend
import RPv_FIz_ModelFamilies
import RPv_FIz_FamilyLengths
import RPv_FIz_ScalarAssembly
import RPv_FIz_FamilyPacking
import RPv_FIz_SemanticAlignment
import RPv_FIz_CoefficientsOnRun
import RPv_FIz_PackShape
import RPv_FIz_ConcretePack
import RPv_FIz_NormalizationNonvacuity
import RPv_FIz_Retained24
import RPv_FIz_SameComposition
import RPv_FIv_PreparedNewTotal
import RPv_FIz_SelectorSplit
import RPv_FIz_Statements
import RPv_FIz_WideCoefficientsOnRun
import RPv_FIz_Audit
import RPv_FJa_SplitShape
import RPv_FJa_ReverseStep
import RPv_FJj_SuccessorLoop
import RPv_FJj_SuccessorLiteralStep
import RPv_FJj_SuccessorOrder
import RPv_FJj_SuccessorLiteral
import RPv_FJj_SuccessorPoint
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_FIx_HighSumOuter, `RPv_FIx_HighSum, `RPv_FIx_ScheduleModel, `RPv_FIx_ScheduleIndices, `RPv_FIx_InitialWrites, `RPv_FIv_PreparedMul, `RPv_FIx_InitialArray, `RPv_FIx_AbsorptionArray, `RPv_FIx_ScheduleValue, `RPv_FIx_SchedulePacked, `RPv_FIx_PathLiteral, `RPv_FIx_PathModel, `RPv_FIx_PathMeaning, `RPv_FIx_PathPacked, `RPv_FIy_CoefficientSource, `RPv_FIy_IteratorShape, `RPv_FIy_ListDecoded, `RPv_FIy_ScalarPacked, `RPv_FIy_NativeCoefficients, `RPv_FIw_CompositionOrigins, `RPv_FIr_NativeArithmetic, `RPv_FIr_NativeCM, `RPv_FIr_NativeQM, `RPv_FIr_NativeValue, `RPv_FIr_NativeArray, `RPv_FIr_ArrayRead, `RPv_FIr_BuilderCanonical, `RPv_FIr_SelectedClaim, `RPv_FIw_OpeningCanonical, `RPv_FIy_PartialRoot, `RPv_FIy_ScalingSource, `RPv_FIy_ScalingNonvacuity, `RPv_F3X_FixtureRuntime, `RPv_F3X_FixtureSource, `RPv_Rc10_Nonvacuity, `RPv_FIq_Top, `RPv_FIr_Top, `RPv_FIp_Nonvacuity, `RPv_FIq_Nonvacuity, `RPv_FIr_Nonvacuity, `RPv_FIy_Statements, `RPv_FIw_PublicModel, `RPv_FIy_ValueRangeShape, `RPv_FIy_ValueRangeList, `RPv_FIy_ValueFamilyList, `RPv_FIy_Audit, `RPv_FIz_BoxedOrigins, `RPv_FIz_Marginals, `RPv_FIz_RangeFold, `RPv_FIz_RangeMarginal, `RPv_FIz_ScheduleNodes, `RPv_FIz_InitialShape, `RPv_FIz_ScheduleShape, `RPv_FIz_ScheduleInitial, `RPv_FIz_ScheduleAbsorption, `RPv_FIz_ScheduleFamily, `RPv_FIz_PathList, `RPv_FIz_PathSelector, `RPv_FIz_PathFamily, `RPv_FIz_OccupancyFamily, `RPv_FIz_DigestRead, `RPv_FIz_DigestBinding, `RPv_FIz_DigestPrefix, `RPv_FIz_EmptyRoots, `RPv_FIz_EmptyBound, `RPv_FIz_EmptyRight, `RPv_FIz_DigestFrontier, `RPv_FIz_DigestFold, `RPv_FIz_DigestSuffix, `RPv_FIz_PublicDigest, `RPv_FIz_DigestFamily, `RPv_FIz_ScalarFamily, `RPv_FIz_ScalarList, `RPv_FIz_SelectedList, `RPv_FIz_ContributionList, `RPv_FIz_PackLinear, `RPv_FIz_ContributionAppend, `RPv_FIz_ModelFamilies, `RPv_FIz_FamilyLengths, `RPv_FIz_ScalarAssembly, `RPv_FIz_FamilyPacking, `RPv_FIz_SemanticAlignment, `RPv_FIz_CoefficientsOnRun, `RPv_FIz_PackShape, `RPv_FIz_ConcretePack, `RPv_FIz_NormalizationNonvacuity, `RPv_FIz_Retained24, `RPv_FIz_SameComposition, `RPv_FIv_PreparedNewTotal, `RPv_FIz_SelectorSplit, `RPv_FIz_Statements, `RPv_FIz_WideCoefficientsOnRun, `RPv_FIz_Audit, `RPv_FJa_SplitShape, `RPv_FJa_ReverseStep, `RPv_FJj_SuccessorLoop, `RPv_FJj_SuccessorLiteralStep, `RPv_FJj_SuccessorOrder, `RPv_FJj_SuccessorLiteral, `RPv_FJj_SuccessorPoint ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPV_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPV_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPV_AUDIT_COMPLETE declarations={count} modules={selected.size}"
