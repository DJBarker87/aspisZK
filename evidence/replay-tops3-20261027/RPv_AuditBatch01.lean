import Lean
import RPv_FJg_ScalarCell
import RPv_FJg_ScalarFold
import RPv_FJg_ScalarValue
import RPv_FJg_QuarterBase
import RPv_FJg_Quarter
import RPv_FJr_QuarterSquared
import RPv_FJr_InactiveMeaning
import RPv_FJg_ScalarReference
import RPv_FJm_WrappingSuccess
import RPv_FJm_SquareOperand
import RPv_FJm_CMSquareRawTrace
import RPv_FJm_CMSquareOperandJoin
import RPv_FJm_CMSquareTrace
import RPv_FJm_BaseCast
import RPv_FJm_SquareAlgebra
import RPv_FJm_ModSquare
import RPv_FJm_RealSquare
import RPv_FJm_CMSquarePack
import RPv_FJm_CMSquare
import RPv_FJm_QMSquare
import RPv_FJm_LibraStages
import RPv_FJm_LibraTermValue
import RPv_FJr_LibraFactors
import RPv_FJm_LibraBodyCut
import RPv_FJm_LibraPowerValues
import RPv_FJm_LibraTotals
import RPv_FJm_WriteOrder
import RPv_FJm_LibraFinishZero
import RPv_FJm_LibraFinishOne
import RPv_FJr_LibraBodyValues
import RPv_FJr_LibraZero
import RPv_FJr_LibraOne
import RPv_FJm_LibraSomeCut
import RPv_FJm_LibraDone
import RPv_FJr_LibraLoopCuts
import RPv_FJr_LibraWeightsValue
import RPv_FJr_LibraContraction
import RPv_FJr_SparseDot
import RPv_FJr_LibraMeaning
import RPv_FJr_ExtraValue
import RPv_FJj_QMSlice
import RPv_FJm_ExtraCanon
import RPv_FJr_TracePart04
import RPv_FJg_HighCell
import RPv_FJg_HighStep
import RPv_FJg_HighValue
import RPv_FJg_OriginalDigitCanon
import RPv_FJg_SharedPart1
import RPv_FJg_PartialsCell
import RPv_FJg_PartialsValue
import RPv_FJg_FinalContinuation
import RPv_FJg_Part1Final
import RPv_FJg_LowHorner
import RPv_FJg_QuarterHorner
import RPv_FJj_HornerInstances
import RPv_FJj_HornerConcrete
import RPv_FJg_LiteralTensor
import RPv_FJg_OriginalDigitValues
import RPv_FJg_ScaleSum
import RPv_FJj_LowSum
import RPv_FJj_ScaleModel
import RPv_FJg_HighSum
import RPv_FJd_ReferenceDot
import RPv_FJf_PartialReference
import RPv_FJg_PartialSum
import RPv_FJd_HighReference
import RPv_FJj_HighInstances
import RPv_FJj_HighSource
import RPv_FJj_CommonEmbedding
import RPv_FJj_HighReference
import RPv_FJj_Part1Meaning
import RPv_FJj_PointAdvance
import RPv_FJj_PointSecond
import RPv_FJj_SuccessorCell
import RPv_FJj_SuccessorCut
import RPv_FJj_SuccessorBody
import RPv_FJj_SuccessorModel
import RPv_FJj_SuccessorStep
import RPv_FIv_NativeArray
import RPv_FIw_ArrayValue
import RPv_FIy_ArraySlot
import RPv_FIw_SelectorIndices
import RPv_FIy_FrontierBits
import RPv_FIy_Carry
import RPv_FIw_BuilderValue
import RPv_FIx_Builder
import RPv_FIy_MapValue
import RPv_FIw_ScalarArithmetic
import RPv_FIy_DigestTarget
import RPv_EqualityValueSlice
import RPv_EqualityValueAdapter
import RPv_FIv_SubMap
import RPv_FIy_DigestArithmetic
import RPv_FIx_ArithmeticTotal
import RPv_FIx_HighSumInner
import RPv_FIx_PreweightedSelect
import RPv_FIx_PreweightedLanes
import RPv_FIw_ArrayReadValue
import RPv_FIx_ArrayMeaning
import RPv_SelectedClaimSlice
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_FJg_ScalarCell, `RPv_FJg_ScalarFold, `RPv_FJg_ScalarValue, `RPv_FJg_QuarterBase, `RPv_FJg_Quarter, `RPv_FJr_QuarterSquared, `RPv_FJr_InactiveMeaning, `RPv_FJg_ScalarReference, `RPv_FJm_WrappingSuccess, `RPv_FJm_SquareOperand, `RPv_FJm_CMSquareRawTrace, `RPv_FJm_CMSquareOperandJoin, `RPv_FJm_CMSquareTrace, `RPv_FJm_BaseCast, `RPv_FJm_SquareAlgebra, `RPv_FJm_ModSquare, `RPv_FJm_RealSquare, `RPv_FJm_CMSquarePack, `RPv_FJm_CMSquare, `RPv_FJm_QMSquare, `RPv_FJm_LibraStages, `RPv_FJm_LibraTermValue, `RPv_FJr_LibraFactors, `RPv_FJm_LibraBodyCut, `RPv_FJm_LibraPowerValues, `RPv_FJm_LibraTotals, `RPv_FJm_WriteOrder, `RPv_FJm_LibraFinishZero, `RPv_FJm_LibraFinishOne, `RPv_FJr_LibraBodyValues, `RPv_FJr_LibraZero, `RPv_FJr_LibraOne, `RPv_FJm_LibraSomeCut, `RPv_FJm_LibraDone, `RPv_FJr_LibraLoopCuts, `RPv_FJr_LibraWeightsValue, `RPv_FJr_LibraContraction, `RPv_FJr_SparseDot, `RPv_FJr_LibraMeaning, `RPv_FJr_ExtraValue, `RPv_FJj_QMSlice, `RPv_FJm_ExtraCanon, `RPv_FJr_TracePart04, `RPv_FJg_HighCell, `RPv_FJg_HighStep, `RPv_FJg_HighValue, `RPv_FJg_OriginalDigitCanon, `RPv_FJg_SharedPart1, `RPv_FJg_PartialsCell, `RPv_FJg_PartialsValue, `RPv_FJg_FinalContinuation, `RPv_FJg_Part1Final, `RPv_FJg_LowHorner, `RPv_FJg_QuarterHorner, `RPv_FJj_HornerInstances, `RPv_FJj_HornerConcrete, `RPv_FJg_LiteralTensor, `RPv_FJg_OriginalDigitValues, `RPv_FJg_ScaleSum, `RPv_FJj_LowSum, `RPv_FJj_ScaleModel, `RPv_FJg_HighSum, `RPv_FJd_ReferenceDot, `RPv_FJf_PartialReference, `RPv_FJg_PartialSum, `RPv_FJd_HighReference, `RPv_FJj_HighInstances, `RPv_FJj_HighSource, `RPv_FJj_CommonEmbedding, `RPv_FJj_HighReference, `RPv_FJj_Part1Meaning, `RPv_FJj_PointAdvance, `RPv_FJj_PointSecond, `RPv_FJj_SuccessorCell, `RPv_FJj_SuccessorCut, `RPv_FJj_SuccessorBody, `RPv_FJj_SuccessorModel, `RPv_FJj_SuccessorStep, `RPv_FIv_NativeArray, `RPv_FIw_ArrayValue, `RPv_FIy_ArraySlot, `RPv_FIw_SelectorIndices, `RPv_FIy_FrontierBits, `RPv_FIy_Carry, `RPv_FIw_BuilderValue, `RPv_FIx_Builder, `RPv_FIy_MapValue, `RPv_FIw_ScalarArithmetic, `RPv_FIy_DigestTarget, `RPv_EqualityValueSlice, `RPv_EqualityValueAdapter, `RPv_FIv_SubMap, `RPv_FIy_DigestArithmetic, `RPv_FIx_ArithmeticTotal, `RPv_FIx_HighSumInner, `RPv_FIx_PreweightedSelect, `RPv_FIx_PreweightedLanes, `RPv_FIw_ArrayReadValue, `RPv_FIx_ArrayMeaning, `RPv_SelectedClaimSlice ]
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
