import Lean
import RPv_IDa_Deployed
import RPv_FJn_MainArrayValue
import RPv_FIr_GatherCallback
import RPv_FJn_WordRemainder
import RPv_FJa_SquareMap
import RPv_FJa_SquareValue
import RPv_FJa_PoseidonPow5
import RPv_RawPoseidonExtensionSlice
import RPv_RowCallbackSlice
import RPv_RawPoseidonExternalRows
import RPv_RawPoseidonExternalRowClosure
import RPv_RawPoseidonExternalRowReads
import RPv_RawPoseidonExtensionWords
import RPv_FJb_RawConversion
import RPv_FJe_RawLocalCanon
import RPv_RawPoseidonRowField
import RPv_FJe_RawConversionValue
import RPv_ArrayFromFnCopySlice
import RPv_ArrayFromFnCopyStable
import RPv_FJb_BuilderStable
import RPv_FJb_BuilderSelected
import RPv_FJb_BuilderTotal
import RPv_FJh_Base
import RPv_FJk_CarrierRead
import RPv_FJn_GatherCell
import RPv_FIw_SelectedValue
import RPv_FIw_OpeningValues
import RPv_FJk_OpeningSelected
import RPv_FIq_TerminalParts
import RPv_FIr_GatherCanonical
import RPv_FJn_GatherValue
import RPv_FIw_CopyMeaning
import RPv_FIw_CopyTransport
import RPv_FIw_CopyEndpoint
import RPv_FIv_PreparedTotal
import RPv_JFy_FieldTotal
import RPv_JFy_ArrayTotal
import RPv_JFy_SquareMap
import RPv_JFy_SquareTotal
import RPv_JFy_Pow5
import RPv_JFy_Specs
import RPv_JFy_Lift
import RPv_JFy_SelectorRow
import RPv_JFy_Scalars
import RPv_JFy_Steps
import RPv_JGa_LinkShape
import RPv_JGa_LinkChunk00
import RPv_JGa_LinkChunk01
import RPv_JGa_LinkChunk02
import RPv_JGa_LinkChunk03
import RPv_JGa_LinkChunk04
import RPv_JGa_LinkChunk05
import RPv_JGa_LinkChunk06
import RPv_JGa_LinkChunk07
import RPv_JGa_LinkBounds
import RPv_FJk_CopyDescriptor
import RPv_FJk_CopyWeightSimple
import RPv_CopyLinkBitArithmetic
import RPv_FJk_CopyWeightBits
import RPv_FJk_CopyWeightValue
import RPv_FJk_CopyStep
import RPv_FJk_CopyRegistry
import RPv_FJk_CopyFold
import RPv_JFy_ZeroArrays
import RPv_FJk_CopyFullFold
import RPv_FIw_CopyEvaluation
import RPv_FJk_CopyRowTransport
import RPv_FJn_ClaimsModel
import RPv_FJn_GatherProjection
import RPv_FIr_CarrierCanonical
import RPv_FJn_MainClaims
import RPv_FIp_MaskNativeValue
import RPv_FJn_MaskInputCanonical
import RPv_FIp_MaskValue
import RPv_FJn_MaskDecode
import RPv_ExtractedMaskCoefficientDecode
import RPv_ExtractedMaskCoefficientWriteMeaning
import RPv_ExtractedMaskCoefficientLoopMeaning
import RPv_ExtractedMaskCoefficientScheduledSum
import RPv_ExtractedMaskPopulatedMeaning
import RPv_ExtractedMaskLinearMap
import RPv_ExtractedMaskSemanticBridge
import RPv_ExtractedMaskSemanticBridgeConcrete
import RPv_FJn_MaskWide
import RPv_FJn_MainPoint
import RPv_FJq_MainCells
import RPv_FJq_MainIndices
import RPv_FJq_ClaimRead
import RPv_FIr_MaskedArithmetic
import RPv_FJn_MaskedWideValue
import RPv_JGa_LinkWeightSimple
import RPv_JGa_WeightShift
import RPv_JGa_LinkWeightBits
import RPv_JGa_LinkWeight
import RPv_JFy_PreparedSteps
import RPv_JGa_CopyEndpoint
import RPv_JGa_ArrayProperty
import RPv_JGa_CopyLoop
import RPv_JGa_PatternBounds
import RPv_JGa_PatternCell
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_IDa_Deployed, `RPv_FJn_MainArrayValue, `RPv_FIr_GatherCallback, `RPv_FJn_WordRemainder, `RPv_FJa_SquareMap, `RPv_FJa_SquareValue, `RPv_FJa_PoseidonPow5, `RPv_RawPoseidonExtensionSlice, `RPv_RowCallbackSlice, `RPv_RawPoseidonExternalRows, `RPv_RawPoseidonExternalRowClosure, `RPv_RawPoseidonExternalRowReads, `RPv_RawPoseidonExtensionWords, `RPv_FJb_RawConversion, `RPv_FJe_RawLocalCanon, `RPv_RawPoseidonRowField, `RPv_FJe_RawConversionValue, `RPv_ArrayFromFnCopySlice, `RPv_ArrayFromFnCopyStable, `RPv_FJb_BuilderStable, `RPv_FJb_BuilderSelected, `RPv_FJb_BuilderTotal, `RPv_FJh_Base, `RPv_FJk_CarrierRead, `RPv_FJn_GatherCell, `RPv_FIw_SelectedValue, `RPv_FIw_OpeningValues, `RPv_FJk_OpeningSelected, `RPv_FIq_TerminalParts, `RPv_FIr_GatherCanonical, `RPv_FJn_GatherValue, `RPv_FIw_CopyMeaning, `RPv_FIw_CopyTransport, `RPv_FIw_CopyEndpoint, `RPv_FIv_PreparedTotal, `RPv_JFy_FieldTotal, `RPv_JFy_ArrayTotal, `RPv_JFy_SquareMap, `RPv_JFy_SquareTotal, `RPv_JFy_Pow5, `RPv_JFy_Specs, `RPv_JFy_Lift, `RPv_JFy_SelectorRow, `RPv_JFy_Scalars, `RPv_JFy_Steps, `RPv_JGa_LinkShape, `RPv_JGa_LinkChunk00, `RPv_JGa_LinkChunk01, `RPv_JGa_LinkChunk02, `RPv_JGa_LinkChunk03, `RPv_JGa_LinkChunk04, `RPv_JGa_LinkChunk05, `RPv_JGa_LinkChunk06, `RPv_JGa_LinkChunk07, `RPv_JGa_LinkBounds, `RPv_FJk_CopyDescriptor, `RPv_FJk_CopyWeightSimple, `RPv_CopyLinkBitArithmetic, `RPv_FJk_CopyWeightBits, `RPv_FJk_CopyWeightValue, `RPv_FJk_CopyStep, `RPv_FJk_CopyRegistry, `RPv_FJk_CopyFold, `RPv_JFy_ZeroArrays, `RPv_FJk_CopyFullFold, `RPv_FIw_CopyEvaluation, `RPv_FJk_CopyRowTransport, `RPv_FJn_ClaimsModel, `RPv_FJn_GatherProjection, `RPv_FIr_CarrierCanonical, `RPv_FJn_MainClaims, `RPv_FIp_MaskNativeValue, `RPv_FJn_MaskInputCanonical, `RPv_FIp_MaskValue, `RPv_FJn_MaskDecode, `RPv_ExtractedMaskCoefficientDecode, `RPv_ExtractedMaskCoefficientWriteMeaning, `RPv_ExtractedMaskCoefficientLoopMeaning, `RPv_ExtractedMaskCoefficientScheduledSum, `RPv_ExtractedMaskPopulatedMeaning, `RPv_ExtractedMaskLinearMap, `RPv_ExtractedMaskSemanticBridge, `RPv_ExtractedMaskSemanticBridgeConcrete, `RPv_FJn_MaskWide, `RPv_FJn_MainPoint, `RPv_FJq_MainCells, `RPv_FJq_MainIndices, `RPv_FJq_ClaimRead, `RPv_FIr_MaskedArithmetic, `RPv_FJn_MaskedWideValue, `RPv_JGa_LinkWeightSimple, `RPv_JGa_WeightShift, `RPv_JGa_LinkWeightBits, `RPv_JGa_LinkWeight, `RPv_JFy_PreparedSteps, `RPv_JGa_CopyEndpoint, `RPv_JGa_ArrayProperty, `RPv_JGa_CopyLoop, `RPv_JGa_PatternBounds, `RPv_JGa_PatternCell ]
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
