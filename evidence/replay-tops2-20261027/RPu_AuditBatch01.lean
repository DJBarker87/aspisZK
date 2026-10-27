import Lean
import RPu_JFv_TX2_FoldResidue
import RPu_FJi_SumBlocks
import RPu_JFs_TX2_RawMath
import RPu_JFs_TX2_RawMap
import RPu_JFs_TX2_Raw
import RPu_FJf_RawReference
import RPu_FJf_RawArithmetic
import RPu_FJf_RawFoldBound
import RPu_FJf_RawUV
import RPu_FJf_Raw23
import RPu_FJf_Raw01
import RPu_FJf_RawResidue
import RPu_FJf_RawTower
import RPu_FJf_RawField
import RPu_FJf_DotLane
import RPu_FJf_DotLaneDone
import RPu_FJf_DotLaneStep
import RPu_FJf_DotPushValue
import RPu_JFs_TX2_CanonicalReduce
import RPu_JFv_TX2_CanonicalMeaning
import RPu_JFs_TX2_Reduce
import RPu_JFs_TX2_FromLimbs
import RPu_JFs_TX2_DotFinish
import RPu_JFv_TX2_DotFinishMeaning
import RPu_FJf_DotFinishValue
import RPu_FJf_RawDecode
import RPu_FJf_DotBound
import RPu_FJf_DotMeaning
import RPu_JFr_TX2_TailRead
import RPu_JFs_TX2_TailCanonical
import RPu_JFs_TX2_TailQM
import RPu_JFs_TX2_CheckedQ
import RPu_FJf_EbyKCodec
import RPu_FJf_EbyKPush
import RPu_FJi_WidePack
import RPu_JFv_TX2_FromLimbsMeaning
import RPu_JFs_TX2_Outer
import RPu_JFs_TX2_DotSuffix
import RPu_JFs_TX2_ScalarFinish
import RPu_JFv_TX2_ScalarMeaning
import RPu_FJi_HeadValue
import RPu_FIp_ArrayValue
import RPu_FJi_PackCoefficient
import RPu_FJi_PackProduct
import RPu_FJi_BaseDot
import RPu_FJi_HeadCanonical
import RPu_FIq_NativeTypes
import RPu_FIq_NativeExternal
import RPu_FIq_Native01
import RPu_FIq_Native02
import RPu_FIv_Arithmetic
import RPu_FIw_WordValue
import RPu_FJi_TailInputs
import RPu_FJi_DecodeM31
import RPu_FJi_DecodeCM31
import RPu_FJi_DecodeQM31
import RPu_FJi_DecodeUnwrap
import RPu_FJf_FromLimbsPacked
import RPu_FJf_EbyKFinish
import RPu_FJf_EbyKNew
import RPu_FJi_TailTrace
import RPu_FJi_SlotValue
import RPu_FJl_TermRead
import RPu_FJl_InnerReads
import RPu_FJl_OuterReads
import RPu_FJl_TailReads
import RPu_FJl_SlotReads
import RPu_FJl_M31Refine
import RPu_FJl_ByteArray
import RPu_FJl_M31ArrayValue
import RPu_FJl_ScalarWindow
import RPu_FJl_SliceCopy
import RPu_FJl_FixedIndex
import RPu_FJl_C1Coordinates
import RPu_FJl_WindowArithmetic
import RPu_FJl_ScalarLiteral
import RPu_FJl_ScalarValues
import RPu_FJl_BaseLiteral
import RPu_FJl_CMParser
import RPu_FJl_QMParser
import RPu_FJl_QMCodec
import RPu_FJl_QMArrayValue
import RPu_FJl_QMSliceValue
import RPu_FJl_QMWindow
import RPu_FJl_TailWindow0
import RPu_FJl_TailWindow1
import RPu_FJl_TailWindow2
import RPu_FJl_C2Coordinates
import RPu_FJl_TailLiteral
import RPu_FJl_SlotLiteral
import RPu_FJo_CircleModel
import RPu_FJp_QueryLaw
import RPu_FJp_Fin22
import RPu_FJo_FourCalls
import RPu_FJo_FixedAssemble
import RPu_FJo_ScalarDecode
import RPu_FJo_C1SlotDecode
import RPu_FJo_C2SlotDecode
import RPu_FJi_PrefixValue
import RPu_FJo_PrefixBytes
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPu_JFv_TX2_FoldResidue, `RPu_FJi_SumBlocks, `RPu_JFs_TX2_RawMath, `RPu_JFs_TX2_RawMap, `RPu_JFs_TX2_Raw, `RPu_FJf_RawReference, `RPu_FJf_RawArithmetic, `RPu_FJf_RawFoldBound, `RPu_FJf_RawUV, `RPu_FJf_Raw23, `RPu_FJf_Raw01, `RPu_FJf_RawResidue, `RPu_FJf_RawTower, `RPu_FJf_RawField, `RPu_FJf_DotLane, `RPu_FJf_DotLaneDone, `RPu_FJf_DotLaneStep, `RPu_FJf_DotPushValue, `RPu_JFs_TX2_CanonicalReduce, `RPu_JFv_TX2_CanonicalMeaning, `RPu_JFs_TX2_Reduce, `RPu_JFs_TX2_FromLimbs, `RPu_JFs_TX2_DotFinish, `RPu_JFv_TX2_DotFinishMeaning, `RPu_FJf_DotFinishValue, `RPu_FJf_RawDecode, `RPu_FJf_DotBound, `RPu_FJf_DotMeaning, `RPu_JFr_TX2_TailRead, `RPu_JFs_TX2_TailCanonical, `RPu_JFs_TX2_TailQM, `RPu_JFs_TX2_CheckedQ, `RPu_FJf_EbyKCodec, `RPu_FJf_EbyKPush, `RPu_FJi_WidePack, `RPu_JFv_TX2_FromLimbsMeaning, `RPu_JFs_TX2_Outer, `RPu_JFs_TX2_DotSuffix, `RPu_JFs_TX2_ScalarFinish, `RPu_JFv_TX2_ScalarMeaning, `RPu_FJi_HeadValue, `RPu_FIp_ArrayValue, `RPu_FJi_PackCoefficient, `RPu_FJi_PackProduct, `RPu_FJi_BaseDot, `RPu_FJi_HeadCanonical, `RPu_FIq_NativeTypes, `RPu_FIq_NativeExternal, `RPu_FIq_Native01, `RPu_FIq_Native02, `RPu_FIv_Arithmetic, `RPu_FIw_WordValue, `RPu_FJi_TailInputs, `RPu_FJi_DecodeM31, `RPu_FJi_DecodeCM31, `RPu_FJi_DecodeQM31, `RPu_FJi_DecodeUnwrap, `RPu_FJf_FromLimbsPacked, `RPu_FJf_EbyKFinish, `RPu_FJf_EbyKNew, `RPu_FJi_TailTrace, `RPu_FJi_SlotValue, `RPu_FJl_TermRead, `RPu_FJl_InnerReads, `RPu_FJl_OuterReads, `RPu_FJl_TailReads, `RPu_FJl_SlotReads, `RPu_FJl_M31Refine, `RPu_FJl_ByteArray, `RPu_FJl_M31ArrayValue, `RPu_FJl_ScalarWindow, `RPu_FJl_SliceCopy, `RPu_FJl_FixedIndex, `RPu_FJl_C1Coordinates, `RPu_FJl_WindowArithmetic, `RPu_FJl_ScalarLiteral, `RPu_FJl_ScalarValues, `RPu_FJl_BaseLiteral, `RPu_FJl_CMParser, `RPu_FJl_QMParser, `RPu_FJl_QMCodec, `RPu_FJl_QMArrayValue, `RPu_FJl_QMSliceValue, `RPu_FJl_QMWindow, `RPu_FJl_TailWindow0, `RPu_FJl_TailWindow1, `RPu_FJl_TailWindow2, `RPu_FJl_C2Coordinates, `RPu_FJl_TailLiteral, `RPu_FJl_SlotLiteral, `RPu_FJo_CircleModel, `RPu_FJp_QueryLaw, `RPu_FJp_Fin22, `RPu_FJo_FourCalls, `RPu_FJo_FixedAssemble, `RPu_FJo_ScalarDecode, `RPu_FJo_C1SlotDecode, `RPu_FJo_C2SlotDecode, `RPu_FJi_PrefixValue, `RPu_FJo_PrefixBytes ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPU_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPU_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPU_AUDIT_COMPLETE declarations={count} modules={selected.size}"
