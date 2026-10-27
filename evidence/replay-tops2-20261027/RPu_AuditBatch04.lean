import Lean
import RPu_FIq_S_RawActualDecodeKInitialLowClaim
import RPu_FIq_S_RawActualAnnotatedTypedRowReadback
import RPu_FIq_S_RecordFrameDropPayload
import RPu_FIq_TypedInitial
import RPu_FIq_S_RawActualDecodedTypedPolynomialAgreement
import RPu_FIq_S_TypedSemanticPolynomialRowFrame
import RPu_FIq_S_TypedSemanticPolynomialRowPayload
import RPu_FIq_S_RawActualPolynomialRowAgreement
import RPu_FIq_S_RawActualAnnotatedPolynomialRowAgreementConsumer
import RPu_FIq_TypedPolynomials
import RPu_FIq_TypedData
import RPu_FIr_SourceInitial
import RPu_FIr_LiteralRow
import RPu_FIr_LiteralValues
import RPu_FIr_PhysicalInitial
import RPu_FIr_EntryIndex
import RPu_FIr_Chain
import RPu_FIr_ChallengeValue
import RPu_FIr_SourceChain
import RPu_FIr_SampleRange
import RPu_FIr_TranscriptRange
import RPu_FIr_AlphaLiteral
import RPu_FIr_PhysicalChain
import RPu_FIr_Remaining
import RPu_FIr_GlobalOwners
import RPu_FIr_GlobalOwners2
import RPu_FJu_Remaining
import RPu_FJu_GlobalOwners
import RPu_FJu_Finish
import RPu_FJu_NativeLiteral
import RPu_FJu_Cont
import RPu_FJu_Caller
import RPu_FJu_Result
import RPu_FJu_Top
import RPu_FJs_GlobalFields
import RPu_FJc_ByteCarrier
import RPu_FJc_LimbParser
import RPu_FJc_ByteParser
import RPu_FJc_FieldBytes
import RPu_FJc_FieldOffsets
import RPu_FJc_FieldValue
import RPu_FJc_ArrayUpdateValue
import RPu_FJc_InactiveCoefficientsModel
import RPu_FIo_GroupSubset
import RPu_FJc_MaskBits
import RPu_FJc_SubsetModel
import RPu_FJc_GroupTable
import RPu_FJc_S2Rows
import RPu_FJr_InactiveRegistry
import RPu_FJg_TensorDigits
import RPu_FJr_InactiveRowIndex
import RPu_FJc_MaskTable0
import RPu_FJc_MaskTable1
import RPu_FJc_MaskTable2
import RPu_FJc_MaskTable3
import RPu_FJc_MaskTable
import RPu_FJr_InactiveRaw
import RPu_FJg_TensorProduct
import RPu_FJg_DualTensor
import RPu_FJm_LibraModel
import RPu_FJf_FactorArray
import RPu_FJf_PointIndices
import RPu_FJf_Coordinates
import RPu_FJf_DigitValue
import RPu_FJf_PointCell
import RPu_FJf_PointDone
import RPu_FJf_PointStep
import RPu_FJf_PointLoop
import RPu_FJf_PointFrame
import RPu_FJf_PointOuterBody
import RPu_FJf_PointOuterFrame
import RPu_FJf_PointFirst
import RPu_FJf_OriginalPoint
import RPu_FJf_CircleBody
import RPu_FJf_CircleIndex
import RPu_FJf_CircleFrame
import RPu_FJf_CircleOuterBody
import RPu_FJf_CircleOuterFrame
import RPu_FJf_FactorZeros
import RPu_FJf_OriginalFactors
import RPu_FJf_ModelPoint
import RPu_FJc_SharedSelf
import RPu_FJc_DigitIndices
import RPu_FIo_ScaleValues
import RPu_FGm_QMScaleValue
import RPu_FGm_WideScaleValue
import RPu_FJc_LowModel
import RPu_FJc_LowCell
import RPu_FJc_LowStep
import RPu_FIo_GroupCoefficients
import RPu_FIo_GroupContract
import RPu_FIo_GroupCanonical
import RPu_FJc_LowValue
import RPu_FJc_LibraFrame
import RPu_FIp_Prefix
import RPu_FIp_FinalSumStep
import RPu_FIp_FinalSum
import RPu_FIp_FinalSumAliases
import RPu_FJc_PairInactiveTrace
import RPu_FJc_InactiveCoefficientsStep
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPu_FIq_S_RawActualDecodeKInitialLowClaim, `RPu_FIq_S_RawActualAnnotatedTypedRowReadback, `RPu_FIq_S_RecordFrameDropPayload, `RPu_FIq_TypedInitial, `RPu_FIq_S_RawActualDecodedTypedPolynomialAgreement, `RPu_FIq_S_TypedSemanticPolynomialRowFrame, `RPu_FIq_S_TypedSemanticPolynomialRowPayload, `RPu_FIq_S_RawActualPolynomialRowAgreement, `RPu_FIq_S_RawActualAnnotatedPolynomialRowAgreementConsumer, `RPu_FIq_TypedPolynomials, `RPu_FIq_TypedData, `RPu_FIr_SourceInitial, `RPu_FIr_LiteralRow, `RPu_FIr_LiteralValues, `RPu_FIr_PhysicalInitial, `RPu_FIr_EntryIndex, `RPu_FIr_Chain, `RPu_FIr_ChallengeValue, `RPu_FIr_SourceChain, `RPu_FIr_SampleRange, `RPu_FIr_TranscriptRange, `RPu_FIr_AlphaLiteral, `RPu_FIr_PhysicalChain, `RPu_FIr_Remaining, `RPu_FIr_GlobalOwners, `RPu_FIr_GlobalOwners2, `RPu_FJu_Remaining, `RPu_FJu_GlobalOwners, `RPu_FJu_Finish, `RPu_FJu_NativeLiteral, `RPu_FJu_Cont, `RPu_FJu_Caller, `RPu_FJu_Result, `RPu_FJu_Top, `RPu_FJs_GlobalFields, `RPu_FJc_ByteCarrier, `RPu_FJc_LimbParser, `RPu_FJc_ByteParser, `RPu_FJc_FieldBytes, `RPu_FJc_FieldOffsets, `RPu_FJc_FieldValue, `RPu_FJc_ArrayUpdateValue, `RPu_FJc_InactiveCoefficientsModel, `RPu_FIo_GroupSubset, `RPu_FJc_MaskBits, `RPu_FJc_SubsetModel, `RPu_FJc_GroupTable, `RPu_FJc_S2Rows, `RPu_FJr_InactiveRegistry, `RPu_FJg_TensorDigits, `RPu_FJr_InactiveRowIndex, `RPu_FJc_MaskTable0, `RPu_FJc_MaskTable1, `RPu_FJc_MaskTable2, `RPu_FJc_MaskTable3, `RPu_FJc_MaskTable, `RPu_FJr_InactiveRaw, `RPu_FJg_TensorProduct, `RPu_FJg_DualTensor, `RPu_FJm_LibraModel, `RPu_FJf_FactorArray, `RPu_FJf_PointIndices, `RPu_FJf_Coordinates, `RPu_FJf_DigitValue, `RPu_FJf_PointCell, `RPu_FJf_PointDone, `RPu_FJf_PointStep, `RPu_FJf_PointLoop, `RPu_FJf_PointFrame, `RPu_FJf_PointOuterBody, `RPu_FJf_PointOuterFrame, `RPu_FJf_PointFirst, `RPu_FJf_OriginalPoint, `RPu_FJf_CircleBody, `RPu_FJf_CircleIndex, `RPu_FJf_CircleFrame, `RPu_FJf_CircleOuterBody, `RPu_FJf_CircleOuterFrame, `RPu_FJf_FactorZeros, `RPu_FJf_OriginalFactors, `RPu_FJf_ModelPoint, `RPu_FJc_SharedSelf, `RPu_FJc_DigitIndices, `RPu_FIo_ScaleValues, `RPu_FGm_QMScaleValue, `RPu_FGm_WideScaleValue, `RPu_FJc_LowModel, `RPu_FJc_LowCell, `RPu_FJc_LowStep, `RPu_FIo_GroupCoefficients, `RPu_FIo_GroupContract, `RPu_FIo_GroupCanonical, `RPu_FJc_LowValue, `RPu_FJc_LibraFrame, `RPu_FIp_Prefix, `RPu_FIp_FinalSumStep, `RPu_FIp_FinalSum, `RPu_FIp_FinalSumAliases, `RPu_FJc_PairInactiveTrace, `RPu_FJc_InactiveCoefficientsStep ]
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
