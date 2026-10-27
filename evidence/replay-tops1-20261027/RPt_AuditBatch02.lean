import Lean
import RPt_ARS_ReachedBudget
import RPt_ARS_ReachedCharge
import RPt_ARS_ReachedMass
import RPt_ARS_ReachedNumeric
import RPt_ART_StartCharge
import RPt_ARU_Charges
import RPt_BEn_AccountComposition
import RPt_BEn_AdmittedCuts
import RPt_BEn_Top
import RPt_FJl_CallIndex
import RPt_FJl_LoopExtraction
import RPt_FJl_Tx1Extraction
import RPt_FJl_Tx2Extraction
import RPt_FJl_QueryExtraction
import RPt_FJl_PairExtraction
import RPt_FJl_SourceSlots
import RPt_FJo_PhaseSlots
import RPt_FIo_ScalarBridge
import RPt_FIo_FieldBridge
import RPt_FIo_ReduceFacts
import RPt_FIo_ReduceBounds
import RPt_FIo_ReduceBridge
import RPt_FIo_M31MulBridge
import RPt_FIo_M31Bridge
import RPt_FIo_M31SubBridge
import RPt_FIo_M31Values
import RPt_FIo_CMValues
import RPt_FIo_QMValues
import RPt_FIo_WideValues
import RPt_FIo_CMProduct
import RPt_FIo_ReduceValues
import RPt_FIo_CMMulValues
import RPt_FIo_ByRValues
import RPt_FIo_QMMulValues
import RPt_FIo_MulUValues
import RPt_FIo_WideMulValues
import RPt_FIo_Constants
import RPt_FIo_FromLimbs
import RPt_FIp_FastFinishCanonical
import RPt_FIp_FromLimbsUnwrap
import RPt_FIp_DotsCanonical
import RPt_FIo_FromBytes
import RPt_FIo_FieldCanonical
import RPt_FIo_ArrayCanon
import RPt_FIp_DotsReached
import RPt_FIp_DotsAllCanonical
import RPt_FIp_DotsOutputCanonical
import RPt_FIp_EqualityValue
import RPt_FIp_SemanticValues
import RPt_FIp_InstalledLaws
import RPt_FIp_FirstMatch
import RPt_FJo_ObservedCircle
import RPt_FJp_PhaseReady
import RPt_FJo_CircleCoefficients
import RPt_FJo_CircleGeneric
import RPt_FJc_PartNames
import RPt_FJc_Constructor
import RPt_FJc_WeightScalarBridge
import RPt_FJc_WeightCMBridge
import RPt_FJc_WeightCMMul
import RPt_FJc_WeightByR
import RPt_FJc_WeightQMBridge
import RPt_FJc_WeightQMMul
import RPt_FJc_WeightValues
import RPt_FJc_WeightConstants
import RPt_FJd_PointReference
import RPt_FJd_SourceFactor
import RPt_FJc_InstalledParts
import RPt_FJc_ArrayRead
import RPt_FJc_WeightArray
import RPt_FIo_LoopInvariant
import RPt_FIo_RangeNext
import RPt_FJf_PointBody
import RPt_FJf_ArrayOps
import RPt_FJf_ArraySlots
import RPt_FJc_ReadSlot
import RPt_FJf_U64Array
import RPt_FIp_RangeNone
import RPt_FJi_Accumulations
import RPt_T2Nat_ReaderNonvacuity
import RPt_JFq_Raw
import RPt_JFq_Range
import RPt_JFq_Scalar
import RPt_JFq_State
import RPt_JFq_Root0
import RPt_JFq_Root1
import RPt_JFq_Gamma
import RPt_JFq_Kappa
import RPt_JFq_Alpha0
import RPt_JFq_Alpha1
import RPt_JFq_Rho
import RPt_JFq_QueryWords
import RPt_JFq_Queries
import RPt_JFq_Sem00
import RPt_JFq_Sem01
import RPt_JFq_Sem02
import RPt_JFq_Sem03
import RPt_JFq_Sem04
import RPt_JFq_Sem05
import RPt_JFq_Sem06
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPt_ARS_ReachedBudget, `RPt_ARS_ReachedCharge, `RPt_ARS_ReachedMass, `RPt_ARS_ReachedNumeric, `RPt_ART_StartCharge, `RPt_ARU_Charges, `RPt_BEn_AccountComposition, `RPt_BEn_AdmittedCuts, `RPt_BEn_Top, `RPt_FJl_CallIndex, `RPt_FJl_LoopExtraction, `RPt_FJl_Tx1Extraction, `RPt_FJl_Tx2Extraction, `RPt_FJl_QueryExtraction, `RPt_FJl_PairExtraction, `RPt_FJl_SourceSlots, `RPt_FJo_PhaseSlots, `RPt_FIo_ScalarBridge, `RPt_FIo_FieldBridge, `RPt_FIo_ReduceFacts, `RPt_FIo_ReduceBounds, `RPt_FIo_ReduceBridge, `RPt_FIo_M31MulBridge, `RPt_FIo_M31Bridge, `RPt_FIo_M31SubBridge, `RPt_FIo_M31Values, `RPt_FIo_CMValues, `RPt_FIo_QMValues, `RPt_FIo_WideValues, `RPt_FIo_CMProduct, `RPt_FIo_ReduceValues, `RPt_FIo_CMMulValues, `RPt_FIo_ByRValues, `RPt_FIo_QMMulValues, `RPt_FIo_MulUValues, `RPt_FIo_WideMulValues, `RPt_FIo_Constants, `RPt_FIo_FromLimbs, `RPt_FIp_FastFinishCanonical, `RPt_FIp_FromLimbsUnwrap, `RPt_FIp_DotsCanonical, `RPt_FIo_FromBytes, `RPt_FIo_FieldCanonical, `RPt_FIo_ArrayCanon, `RPt_FIp_DotsReached, `RPt_FIp_DotsAllCanonical, `RPt_FIp_DotsOutputCanonical, `RPt_FIp_EqualityValue, `RPt_FIp_SemanticValues, `RPt_FIp_InstalledLaws, `RPt_FIp_FirstMatch, `RPt_FJo_ObservedCircle, `RPt_FJp_PhaseReady, `RPt_FJo_CircleCoefficients, `RPt_FJo_CircleGeneric, `RPt_FJc_PartNames, `RPt_FJc_Constructor, `RPt_FJc_WeightScalarBridge, `RPt_FJc_WeightCMBridge, `RPt_FJc_WeightCMMul, `RPt_FJc_WeightByR, `RPt_FJc_WeightQMBridge, `RPt_FJc_WeightQMMul, `RPt_FJc_WeightValues, `RPt_FJc_WeightConstants, `RPt_FJd_PointReference, `RPt_FJd_SourceFactor, `RPt_FJc_InstalledParts, `RPt_FJc_ArrayRead, `RPt_FJc_WeightArray, `RPt_FIo_LoopInvariant, `RPt_FIo_RangeNext, `RPt_FJf_PointBody, `RPt_FJf_ArrayOps, `RPt_FJf_ArraySlots, `RPt_FJc_ReadSlot, `RPt_FJf_U64Array, `RPt_FIp_RangeNone, `RPt_FJi_Accumulations, `RPt_T2Nat_ReaderNonvacuity, `RPt_JFq_Raw, `RPt_JFq_Range, `RPt_JFq_Scalar, `RPt_JFq_State, `RPt_JFq_Root0, `RPt_JFq_Root1, `RPt_JFq_Gamma, `RPt_JFq_Kappa, `RPt_JFq_Alpha0, `RPt_JFq_Alpha1, `RPt_JFq_Rho, `RPt_JFq_QueryWords, `RPt_JFq_Queries, `RPt_JFq_Sem00, `RPt_JFq_Sem01, `RPt_JFq_Sem02, `RPt_JFq_Sem03, `RPt_JFq_Sem04, `RPt_JFq_Sem05, `RPt_JFq_Sem06 ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPT_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPT_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPT_AUDIT_COMPLETE declarations={count} modules={selected.size}"
