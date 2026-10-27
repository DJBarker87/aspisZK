import Lean
import RPt_BEf_Carrier
import RPt_BEi_Execution
import RPt_BEi_ExecutionComplete
import RPt_BEi_ExecutionUnique
import RPt_BEi_ExecutionHistory
import RPt_BEf_Bind
import RPt_BEg_Observation
import RPt_BEh_Scope
import RPt_BEi_CutProjection
import RPt_BEi_RecorderCut
import RPt_BEf_Pure
import RPt_BEf_Batches
import RPt_BEi_BatchCut
import RPt_BEi_BatchPrefix
import RPt_BEj_ReifiedBatch
import RPt_BEj_BatchValue
import RPt_BEk_Projection
import RPt_BEl_Recorder
import RPt_BEl_PartialRecorder
import RPt_BEg_Simulation
import RPt_BEl_LeafReference
import RPt_BEl_CodeCongr
import RPt_BEl_BatchStep
import RPt_BEl_BatchLoop
import RPt_BEl_BatchTree
import RPt_BEl_Batch
import RPt_BEl_ReferenceSource
import RPt_BEl_WeakObservation
import RPt_BEl_NativeBatchCut
import RPt_BEk_QueryPrefix
import RPt_BEj_LocalExport
import RPt_BEj_SlotExport
import RPt_BEk_CutExport
import RPt_ARU_Returning
import RPt_BEk_Returning
import RPt_BEk_SlotExport
import RPt_BEl_SlotObservation
import RPt_BEk_ReachedInputs
import RPt_BEf_Fold
import RPt_BEf_Offset
import RPt_BEf_Count
import RPt_BEl_ReachedReference
import RPt_BEl_OriginalReference
import RPt_RPx_Rejected
import RPt_RPx_Accounting
import RPt_RPx_Prefix
import RPt_RPx_Transport
import RPt_RPx_OuterCredit
import RPt_RPx_LowerBudget
import RPt_RPx_GenericBatch
import RPt_RPx_GenericFirst
import RPt_RPx_GenericSecond
import RPt_RPx_ChildBudget
import RPt_RPx_OuterDecoded
import RPt_RPx_OuterStage1
import RPt_RPx_OuterStage2
import RPt_RPx_WrapperBudget
import RPt_RPx_InstalledBudget
import RPt_RPx_AccountBudget
import RPt_RPx_AccountCharge
import RPt_ARQ_Join
import RPt_BEl_AccountComposition
import RPt_BEl_LogCoordinates
import RPt_BEl_FullLog
import RPt_BEl_CoordinateLog
import RPt_BEl_GateBounds
import RPt_BEl_LawComposition
import RPt_BEl_PrefixRecorder
import RPt_BEl_LocalCut
import RPt_BEl_RawBackend
import RPt_BEk_LocalAssociation
import RPt_BEk_Nonvacuity
import RPt_BEl_Nonvacuity
import RPt_BEl_Packet
import RPt_BEl_PhysicalCut
import RPt_BEl_RecorderErasure
import RPt_BEl_ReferenceObservation
import RPt_BEl_ReturnRecorder
import RPt_BEl_SliceShape
import RPt_BEl_SourceRecords
import RPt_BEl_Top
import RPt_BEl_Statements
import RPt_BEm_Predecessor
import RPt_BEm_PaddingModel
import RPt_BEm_ByteWord
import RPt_BEm_PaddingCut
import RPt_BEm_PaddingNonvacuity
import RPt_BEm_PaddingGeometry
import RPt_BEm_Final
import RPt_BEn_ExtractedTrace
import RPt_BEn_ExtractedSlots
import RPt_BEn_LocalAssociation
import RPt_BEn_SlotExport
import RPt_BEn_ReachedAssociation
import RPt_BEn_OriginalAssociation
import RPt_BEn_ReachedLaws
import RPt_ART_FullCharge
import RPt_ARQ_AccountCharge
import RPt_ARS_AccountDomination
import RPt_ARS_BudgetFromTotal
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPt_BEf_Carrier, `RPt_BEi_Execution, `RPt_BEi_ExecutionComplete, `RPt_BEi_ExecutionUnique, `RPt_BEi_ExecutionHistory, `RPt_BEf_Bind, `RPt_BEg_Observation, `RPt_BEh_Scope, `RPt_BEi_CutProjection, `RPt_BEi_RecorderCut, `RPt_BEf_Pure, `RPt_BEf_Batches, `RPt_BEi_BatchCut, `RPt_BEi_BatchPrefix, `RPt_BEj_ReifiedBatch, `RPt_BEj_BatchValue, `RPt_BEk_Projection, `RPt_BEl_Recorder, `RPt_BEl_PartialRecorder, `RPt_BEg_Simulation, `RPt_BEl_LeafReference, `RPt_BEl_CodeCongr, `RPt_BEl_BatchStep, `RPt_BEl_BatchLoop, `RPt_BEl_BatchTree, `RPt_BEl_Batch, `RPt_BEl_ReferenceSource, `RPt_BEl_WeakObservation, `RPt_BEl_NativeBatchCut, `RPt_BEk_QueryPrefix, `RPt_BEj_LocalExport, `RPt_BEj_SlotExport, `RPt_BEk_CutExport, `RPt_ARU_Returning, `RPt_BEk_Returning, `RPt_BEk_SlotExport, `RPt_BEl_SlotObservation, `RPt_BEk_ReachedInputs, `RPt_BEf_Fold, `RPt_BEf_Offset, `RPt_BEf_Count, `RPt_BEl_ReachedReference, `RPt_BEl_OriginalReference, `RPt_RPx_Rejected, `RPt_RPx_Accounting, `RPt_RPx_Prefix, `RPt_RPx_Transport, `RPt_RPx_OuterCredit, `RPt_RPx_LowerBudget, `RPt_RPx_GenericBatch, `RPt_RPx_GenericFirst, `RPt_RPx_GenericSecond, `RPt_RPx_ChildBudget, `RPt_RPx_OuterDecoded, `RPt_RPx_OuterStage1, `RPt_RPx_OuterStage2, `RPt_RPx_WrapperBudget, `RPt_RPx_InstalledBudget, `RPt_RPx_AccountBudget, `RPt_RPx_AccountCharge, `RPt_ARQ_Join, `RPt_BEl_AccountComposition, `RPt_BEl_LogCoordinates, `RPt_BEl_FullLog, `RPt_BEl_CoordinateLog, `RPt_BEl_GateBounds, `RPt_BEl_LawComposition, `RPt_BEl_PrefixRecorder, `RPt_BEl_LocalCut, `RPt_BEl_RawBackend, `RPt_BEk_LocalAssociation, `RPt_BEk_Nonvacuity, `RPt_BEl_Nonvacuity, `RPt_BEl_Packet, `RPt_BEl_PhysicalCut, `RPt_BEl_RecorderErasure, `RPt_BEl_ReferenceObservation, `RPt_BEl_ReturnRecorder, `RPt_BEl_SliceShape, `RPt_BEl_SourceRecords, `RPt_BEl_Top, `RPt_BEl_Statements, `RPt_BEm_Predecessor, `RPt_BEm_PaddingModel, `RPt_BEm_ByteWord, `RPt_BEm_PaddingCut, `RPt_BEm_PaddingNonvacuity, `RPt_BEm_PaddingGeometry, `RPt_BEm_Final, `RPt_BEn_ExtractedTrace, `RPt_BEn_ExtractedSlots, `RPt_BEn_LocalAssociation, `RPt_BEn_SlotExport, `RPt_BEn_ReachedAssociation, `RPt_BEn_OriginalAssociation, `RPt_BEn_ReachedLaws, `RPt_ART_FullCharge, `RPt_ARQ_AccountCharge, `RPt_ARS_AccountDomination, `RPt_ARS_BudgetFromTotal ]
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
