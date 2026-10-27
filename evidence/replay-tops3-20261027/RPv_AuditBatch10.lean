import Lean
import RPv_FJa_ExpansionMeaning
import RPv_FJa_WeightAppend
import RPv_FJa_WeightPeriod
import RPv_FJa_ExpansionMass
import RPv_FJa_SlicesValue
import RPv_FJa_BoxedMass
import RPv_FJa_BoxedLiteral
import RPv_FJa_WeightBits
import RPv_FJa_TensorAtPoint
import RPv_FJa_BoxedSelAt
import RPv_FJa_SelectorOnRun
import RPv_FJa_PoseidonSelectors
import RPv_FJh_PoseidonOnComposition
import RPv_FJk_Native07Value
import RPv_FJk_SelectorModel
import RPv_FJn_CopySelectors
import RPv_ValueFamilyFieldTransport
import RPv_PathFamilyFieldTransport
import RPv_FJn_SelectorMap
import RPv_FJn_CopyWide
import RPv_FIv_CompositionTrace
import RPv_FIv_Horner24
import RPv_FIv_Horner4
import RPv_FIv_HornerAlgebra
import RPv_FIv_CompositionValue
import RPv_FJk_HornerValue
import RPv_PreparationPublicFieldsCanonical
import RPv_FJa_PublicCopy
import RPv_FJa_PublicBounds
import RPv_FIr_TerminalTrace
import RPv_FIr_NativeScalar
import RPv_FIr_NativeSub
import RPv_FIr_EqualityCell
import RPv_FIr_EqualityLoop
import RPv_FIr_EqualityReach
import RPv_FIr_EqualityShape
import RPv_FIr_EqualityValue
import RPv_FIr_TerminalValue
import RPv_FIr_EqualityProduct
import RPv_FIr_TerminalPartsValue
import RPv_FIr_RootValue
import RPv_FIr_CompositionH1
import RPv_FIr_H1Canonical
import RPv_FJk_CompositionValue
import RPv_FJk_CompositionContext
import RPv_FJk_ArrayList
import RPv_FJk_PolynomialMap
import RPv_TerminalHornerCore
import RPv_ExtractedMaskTerminalHorner
import RPv_FJk_PolynomialHorner
import RPv_FJk_CompositionWideFold
import RPv_DigestFamilyFieldTransport
import RPv_FJk_OccupancyMap
import RPv_FJk_ListMap
import RPv_ScheduleFamilyFieldTransport
import RPv_AssetFamilyFieldTransport
import RPv_FJk_ScalarLaneMap
import RPv_FJk_SemanticWideOnRun
import RPv_FJk_OpeningsModel
import RPv_PoseidonPairMap
import RPv_PoseidonResidualFieldTransport
import RPv_FJk_ResidualWide
import RPv_FJk_PackedWide
import RPv_FJk_PoseidonFamily
import RPv_FJk_ResidualNaturality
import RPv_FJk_FamilyWide
import RPv_FJk_PoseidonPackedAt
import RPv_FJk_PoseidonWideOnRun
import RPv_FJk_CompositionWideOnRun
import RPv_FJn_LaneModel
import RPv_FJn_EqualityMap
import RPv_FJn_H1Index
import RPv_FJn_H1Origin
import RPv_FJn_SelectedValue
import RPv_FJn_CompositionCopyOnRun
import RPv_FIr_RootRefined
import RPv_FJn_TerminalPartsValue
import RPv_FJn_ActiveOnPoint
import RPv_FJn_SelAtMap
import RPv_FJn_ModelInputs
import RPv_FJn_CompositionSeed
import RPv_FJn_LaneTransport
import RPv_FJn_CompositionModel
import RPv_FJn_CompositionActive
import RPv_FJn_ActivePointMap
import RPv_FJn_NativeCarrierBridge
import RPv_FJn_FormulaMap
import RPv_FJn_EqualityArrays
import RPv_FJn_TerminalValueBridge
import RPv_FJn_TerminalFormulaModel
import RPv_FJn_TerminalModel
import RPv_FJn_TerminalClaimsCongr
import RPv_FJn_GatherTerminal
import RPv_FJn_NativeTerminal
import RPv_FJn_MainDecode
import RPv_FJn_MainTerminal
import RPv_FJt_AlphaOnRun
import RPv_FJn_BeginCanonical
import RPv_FJq_ReferenceRecord
import RPv_FJq_ParentRows
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPv_FJa_ExpansionMeaning, `RPv_FJa_WeightAppend, `RPv_FJa_WeightPeriod, `RPv_FJa_ExpansionMass, `RPv_FJa_SlicesValue, `RPv_FJa_BoxedMass, `RPv_FJa_BoxedLiteral, `RPv_FJa_WeightBits, `RPv_FJa_TensorAtPoint, `RPv_FJa_BoxedSelAt, `RPv_FJa_SelectorOnRun, `RPv_FJa_PoseidonSelectors, `RPv_FJh_PoseidonOnComposition, `RPv_FJk_Native07Value, `RPv_FJk_SelectorModel, `RPv_FJn_CopySelectors, `RPv_ValueFamilyFieldTransport, `RPv_PathFamilyFieldTransport, `RPv_FJn_SelectorMap, `RPv_FJn_CopyWide, `RPv_FIv_CompositionTrace, `RPv_FIv_Horner24, `RPv_FIv_Horner4, `RPv_FIv_HornerAlgebra, `RPv_FIv_CompositionValue, `RPv_FJk_HornerValue, `RPv_PreparationPublicFieldsCanonical, `RPv_FJa_PublicCopy, `RPv_FJa_PublicBounds, `RPv_FIr_TerminalTrace, `RPv_FIr_NativeScalar, `RPv_FIr_NativeSub, `RPv_FIr_EqualityCell, `RPv_FIr_EqualityLoop, `RPv_FIr_EqualityReach, `RPv_FIr_EqualityShape, `RPv_FIr_EqualityValue, `RPv_FIr_TerminalValue, `RPv_FIr_EqualityProduct, `RPv_FIr_TerminalPartsValue, `RPv_FIr_RootValue, `RPv_FIr_CompositionH1, `RPv_FIr_H1Canonical, `RPv_FJk_CompositionValue, `RPv_FJk_CompositionContext, `RPv_FJk_ArrayList, `RPv_FJk_PolynomialMap, `RPv_TerminalHornerCore, `RPv_ExtractedMaskTerminalHorner, `RPv_FJk_PolynomialHorner, `RPv_FJk_CompositionWideFold, `RPv_DigestFamilyFieldTransport, `RPv_FJk_OccupancyMap, `RPv_FJk_ListMap, `RPv_ScheduleFamilyFieldTransport, `RPv_AssetFamilyFieldTransport, `RPv_FJk_ScalarLaneMap, `RPv_FJk_SemanticWideOnRun, `RPv_FJk_OpeningsModel, `RPv_PoseidonPairMap, `RPv_PoseidonResidualFieldTransport, `RPv_FJk_ResidualWide, `RPv_FJk_PackedWide, `RPv_FJk_PoseidonFamily, `RPv_FJk_ResidualNaturality, `RPv_FJk_FamilyWide, `RPv_FJk_PoseidonPackedAt, `RPv_FJk_PoseidonWideOnRun, `RPv_FJk_CompositionWideOnRun, `RPv_FJn_LaneModel, `RPv_FJn_EqualityMap, `RPv_FJn_H1Index, `RPv_FJn_H1Origin, `RPv_FJn_SelectedValue, `RPv_FJn_CompositionCopyOnRun, `RPv_FIr_RootRefined, `RPv_FJn_TerminalPartsValue, `RPv_FJn_ActiveOnPoint, `RPv_FJn_SelAtMap, `RPv_FJn_ModelInputs, `RPv_FJn_CompositionSeed, `RPv_FJn_LaneTransport, `RPv_FJn_CompositionModel, `RPv_FJn_CompositionActive, `RPv_FJn_ActivePointMap, `RPv_FJn_NativeCarrierBridge, `RPv_FJn_FormulaMap, `RPv_FJn_EqualityArrays, `RPv_FJn_TerminalValueBridge, `RPv_FJn_TerminalFormulaModel, `RPv_FJn_TerminalModel, `RPv_FJn_TerminalClaimsCongr, `RPv_FJn_GatherTerminal, `RPv_FJn_NativeTerminal, `RPv_FJn_MainDecode, `RPv_FJn_MainTerminal, `RPv_FJt_AlphaOnRun, `RPv_FJn_BeginCanonical, `RPv_FJq_ReferenceRecord, `RPv_FJq_ParentRows ]
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
