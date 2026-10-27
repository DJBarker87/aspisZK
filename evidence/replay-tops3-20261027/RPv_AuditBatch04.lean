import Lean
import RPv_FJj_SuccessorFactors
import RPv_FJj_SuccessorInstalled
import RPv_FJj_SuccessorDigit
import RPv_FJj_TensorPrefix
import RPv_FJj_ArrayReadTotal
import RPv_FJj_HighProductInstances
import RPv_FJj_SuccessorHigh
import RPv_FJm_SuccessorLiteralTensor
import RPv_FJj_KindScaleTrace
import RPv_FJj_QMSliceUpdate
import RPv_FJj_TensorCell
import RPv_FJj_TensorBody
import RPv_FJj_TensorCellValue
import RPv_FJj_TensorIndex
import RPv_FJj_TensorCellLanes
import RPv_FJj_TensorModelAdvance
import RPv_FJj_TensorInner
import RPv_FJj_TensorInnerFull
import RPv_FJj_TensorWidth
import RPv_FJj_TensorOuterCell
import RPv_FJj_TensorOuterBody
import RPv_FJj_TensorOuterStep
import RPv_FJj_TensorOuterLoop
import RPv_FJj_QMOne
import RPv_FJj_TensorTwo
import RPv_FJj_SuccessorRow
import RPv_FJj_SuccessorTensor
import RPv_FJm_KindTwoTrace
import RPv_FJm_VecLens
import RPv_FJj_ByteDotCell
import RPv_FJj_ByteDotStep
import RPv_FJj_ByteDotLoop
import RPv_FJj_ByteDotFinal
import RPv_FJj_SuccessorDot
import RPv_FJj_SuccessorScale
import RPv_FJj_LiteralPointTensor
import RPv_FJm_KindTwoArithmetic
import RPv_FJm_KindTwoMeaning
import RPv_FJm_PairTrace
import RPv_FJm_Filled
import RPv_FJm_Continuation
import RPv_FJm_RegularContinuation
import RPv_FJm_Part2Meaning
import RPv_FJm_AbsorptionTrace
import RPv_FJm_PointThird
import RPv_FJm_AbsorptionPoint
import RPv_FJm_AbsorptionFactors
import RPv_FJm_AbsorptionDigit
import RPv_FJm_AbsorptionScale
import RPv_FJm_AbsorptionHighSource
import RPv_FJm_AbsorptionCommon
import RPv_FJm_AbsorptionHighReference
import RPv_FJm_AbsorptionArithmetic
import RPv_FJm_AbsorptionLiteralTensor
import RPv_FJm_AbsorptionMeaning
import RPv_FJm_Part3Meaning
import RPv_FJr_TracePoints
import RPv_FJr_RegularKindTrace
import RPv_FJr_RowTensor
import RPv_FJr_RowScale
import RPv_FJr_RegularKindMeaning
import RPv_FJr_NativeRow
import RPv_FJr_PointAllCanon
import RPv_FJr_BeforeCircles
import RPv_FJr_CircleOuterCuts
import RPv_FJr_CircleRows
import RPv_FJr_ConstructorCircleRows
import RPv_FJr_KindTwoScratch
import RPv_FJr_KindIndices
import RPv_FJr_CircleParts
import RPv_FJr_TraceCircles
import RPv_FJr_RegularCanonical
import RPv_FJr_KindTwoCanonical
import RPv_FJr_TraceRegularCanonical
import RPv_FJr_SharedCanonical
import RPv_FJr_LibraArrayCanonical
import RPv_FJm_LibraBodyCanonical
import RPv_FJm_LibraCanonical
import RPv_FJr_TracePartsCanonical
import RPv_FJr_PairParts
import RPv_FJr_FoldLinear
import RPv_FJr_FinalSumModel
import RPv_FIo_ConcreteDictionary
import RPv_FJr_PairMeaning
import RPv_FJg_ReaderScalarCanon
import RPv_FJr_SourceCanonical
import RPv_FJr_AlphaPrefix
import RPv_FJr_PreparedCanonical
import RPv_FJr_BodyPairMeaning
import RPv_FJs_PreparedPoint
import RPv_FJs_PreparedCircle
import RPv_FJs_FunctionalWeights
import RPv_FJs_DataFunctionals
import RPv_FJs_CircleRange
import RPv_FJs_OperandAlignment
import RPv_FJs_WideRows
import RPv_FJs_WideWeights
import RPv_FJs_ViewDirect
import RPv_FJs_RowAlignment
import RPv_FJs_PreparedAlphas
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_FJj_SuccessorFactors, `RPv_FJj_SuccessorInstalled, `RPv_FJj_SuccessorDigit, `RPv_FJj_TensorPrefix, `RPv_FJj_ArrayReadTotal, `RPv_FJj_HighProductInstances, `RPv_FJj_SuccessorHigh, `RPv_FJm_SuccessorLiteralTensor, `RPv_FJj_KindScaleTrace, `RPv_FJj_QMSliceUpdate, `RPv_FJj_TensorCell, `RPv_FJj_TensorBody, `RPv_FJj_TensorCellValue, `RPv_FJj_TensorIndex, `RPv_FJj_TensorCellLanes, `RPv_FJj_TensorModelAdvance, `RPv_FJj_TensorInner, `RPv_FJj_TensorInnerFull, `RPv_FJj_TensorWidth, `RPv_FJj_TensorOuterCell, `RPv_FJj_TensorOuterBody, `RPv_FJj_TensorOuterStep, `RPv_FJj_TensorOuterLoop, `RPv_FJj_QMOne, `RPv_FJj_TensorTwo, `RPv_FJj_SuccessorRow, `RPv_FJj_SuccessorTensor, `RPv_FJm_KindTwoTrace, `RPv_FJm_VecLens, `RPv_FJj_ByteDotCell, `RPv_FJj_ByteDotStep, `RPv_FJj_ByteDotLoop, `RPv_FJj_ByteDotFinal, `RPv_FJj_SuccessorDot, `RPv_FJj_SuccessorScale, `RPv_FJj_LiteralPointTensor, `RPv_FJm_KindTwoArithmetic, `RPv_FJm_KindTwoMeaning, `RPv_FJm_PairTrace, `RPv_FJm_Filled, `RPv_FJm_Continuation, `RPv_FJm_RegularContinuation, `RPv_FJm_Part2Meaning, `RPv_FJm_AbsorptionTrace, `RPv_FJm_PointThird, `RPv_FJm_AbsorptionPoint, `RPv_FJm_AbsorptionFactors, `RPv_FJm_AbsorptionDigit, `RPv_FJm_AbsorptionScale, `RPv_FJm_AbsorptionHighSource, `RPv_FJm_AbsorptionCommon, `RPv_FJm_AbsorptionHighReference, `RPv_FJm_AbsorptionArithmetic, `RPv_FJm_AbsorptionLiteralTensor, `RPv_FJm_AbsorptionMeaning, `RPv_FJm_Part3Meaning, `RPv_FJr_TracePoints, `RPv_FJr_RegularKindTrace, `RPv_FJr_RowTensor, `RPv_FJr_RowScale, `RPv_FJr_RegularKindMeaning, `RPv_FJr_NativeRow, `RPv_FJr_PointAllCanon, `RPv_FJr_BeforeCircles, `RPv_FJr_CircleOuterCuts, `RPv_FJr_CircleRows, `RPv_FJr_ConstructorCircleRows, `RPv_FJr_KindTwoScratch, `RPv_FJr_KindIndices, `RPv_FJr_CircleParts, `RPv_FJr_TraceCircles, `RPv_FJr_RegularCanonical, `RPv_FJr_KindTwoCanonical, `RPv_FJr_TraceRegularCanonical, `RPv_FJr_SharedCanonical, `RPv_FJr_LibraArrayCanonical, `RPv_FJm_LibraBodyCanonical, `RPv_FJm_LibraCanonical, `RPv_FJr_TracePartsCanonical, `RPv_FJr_PairParts, `RPv_FJr_FoldLinear, `RPv_FJr_FinalSumModel, `RPv_FIo_ConcreteDictionary, `RPv_FJr_PairMeaning, `RPv_FJg_ReaderScalarCanon, `RPv_FJr_SourceCanonical, `RPv_FJr_AlphaPrefix, `RPv_FJr_PreparedCanonical, `RPv_FJr_BodyPairMeaning, `RPv_FJs_PreparedPoint, `RPv_FJs_PreparedCircle, `RPv_FJs_FunctionalWeights, `RPv_FJs_DataFunctionals, `RPv_FJs_CircleRange, `RPv_FJs_OperandAlignment, `RPv_FJs_WideRows, `RPv_FJs_WideWeights, `RPv_FJs_ViewDirect, `RPv_FJs_RowAlignment, `RPv_FJs_PreparedAlphas ]
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
