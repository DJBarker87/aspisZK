import Lean
import RPz8_F3R_FinishProof
import RPz8_F3V_Finish
import RPz8_F3V_ReadModel
import RPz8_F3Y_ReadModel
import RPz8_FGl_FinishLeaves
import RPz8_FGl_PreparedAt
import RPz8_F3S_FirstTailCode
import RPz8_GExp_LowerLaws
import RPz8_GExp_RunPrefix
import RPz8_GExq_CodeTrace
import RPz8_F3R_SdkPure
import RPz8_F3S_FirstHeader
import RPz8_F3S_Forward
import RPz8_F3S_MapLog
import RPz8_F3S_FirstTailLogs
import RPz8_F3S_RunCalls
import RPz8_F3S_FirstOnRun
import RPz8_RawK_Head
import RPz8_RawK_InitHead
import RPz8_RawK_PublicHead
import RPz8_RawK_VerifyHead
import RPz8_RawK_SemanticHead
import RPz8_RawK_PrepareHead
import RPz8_GExp_LowerTrace
import RPz8_RawK_CodeHead
import RPz8_RawK_FirstHead
import RPz8_GExq_PrepareFrame
import RPz8_GExq_FirstFrame
import RPz8_GExq_FirstRoot
import RPz8_GExq_ContainingRead
import RPz8_GExq_FirstChildRoot
import RPz8_RawK_ChildHead
import RPz8_GExq_RecordLog
import RPz8_RawK_TraceLogs
import RPz8_RawK_EventHead
import RPz8_F3S_Segments
import RPz8_F3S_FirstRecords
import RPz8_F3S_SecondRecords
import RPz8_F3S_TwoRecords
import RPz8_F3S_TwoSegments
import RPz8_GExq_EventGood
import RPz8_RawK_RecordedHead
import RPz8_GExq_OuterGoodTwo
import RPz8_GExq_CallerRecord
import RPz8_F3S_ExactChildren
import RPz8_F3S_ChildLogs
import RPz8_F3S_NativeChildren
import RPz8_F3S_SdkDictionary
import RPz8_F3S_Dictionary
import RPz8_F3S_FirstBase
import RPz8_F3S_FirstPairLog
import RPz8_F3U_FirstCode
import RPz8_F3W_FirstLog
import RPz8_F3W_Runs
import RPz8_F3U_Slice
import RPz8_F3W_SourceLog
import RPz8_F3S_Silent
import RPz8_F3S_Residual
import RPz8_F3S_SecondProvenance
import RPz8_F3S_SecondRoot
import RPz8_F3S_SecondOnRun
import RPz8_F3U_ReaderCode
import RPz8_F3U_SecondCode
import RPz8_F3W_SecondLog
import RPz8_F3Q_BatchNative
import RPz8_F3N_BatchCode
import RPz8_F3N_BatchPrograms
import RPz8_F3Q_BatchSyntax
import RPz8_F3Q_SourceCurrentBatch
import RPz8_F3Q_FirstBatch
import RPz8_F3W_FirstBatch
import RPz8_F3Q_SourceBatch
import RPz8_F3Q_SecondBatch
import RPz8_F3W_SecondBatch
import RPz8_F3Q_CheckpointStage
import RPz8_F3Q_Variant
import RPz8_F3L_CheckpointNumeric
import RPz8_F3N_CheckpointLog
import RPz8_F3W_CheckpointLog
import RPz8_F3N_ModelBody
import RPz8_F3Q_BodyOnRun
import RPz8_F3R_PreparedCut
import RPz8_F3R_ConsPrepared
import RPz8_F3N_AuthenticatedTen
import RPz8_F3N_SourceInput
import RPz8_F3N_ConsSource
import RPz8_F3N_SameRun
import RPz8_F3N_SameRunTen
import RPz8_F3N_SameSecond
import RPz8_F3R_CheckpointNative
import RPz8_F3Q_PreparedCut
import RPz8_F3Q_ConsPrepared
import RPz8_F3R_PairBatches
import RPz8_F3Q_CheckpointLogOnRun
import RPz8_F3Q_CheckpointNative
import RPz8_F3R_PairCheckpointLog
import RPz8_F3N_SecondFinish
import RPz8_F3Q_PairBatches
import RPz8_F3R_PairFinish
import RPz8_F3R_PairModelFinish
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz8_F3R_FinishProof, `RPz8_F3V_Finish, `RPz8_F3V_ReadModel, `RPz8_F3Y_ReadModel, `RPz8_FGl_FinishLeaves, `RPz8_FGl_PreparedAt, `RPz8_F3S_FirstTailCode, `RPz8_GExp_LowerLaws, `RPz8_GExp_RunPrefix, `RPz8_GExq_CodeTrace, `RPz8_F3R_SdkPure, `RPz8_F3S_FirstHeader, `RPz8_F3S_Forward, `RPz8_F3S_MapLog, `RPz8_F3S_FirstTailLogs, `RPz8_F3S_RunCalls, `RPz8_F3S_FirstOnRun, `RPz8_RawK_Head, `RPz8_RawK_InitHead, `RPz8_RawK_PublicHead, `RPz8_RawK_VerifyHead, `RPz8_RawK_SemanticHead, `RPz8_RawK_PrepareHead, `RPz8_GExp_LowerTrace, `RPz8_RawK_CodeHead, `RPz8_RawK_FirstHead, `RPz8_GExq_PrepareFrame, `RPz8_GExq_FirstFrame, `RPz8_GExq_FirstRoot, `RPz8_GExq_ContainingRead, `RPz8_GExq_FirstChildRoot, `RPz8_RawK_ChildHead, `RPz8_GExq_RecordLog, `RPz8_RawK_TraceLogs, `RPz8_RawK_EventHead, `RPz8_F3S_Segments, `RPz8_F3S_FirstRecords, `RPz8_F3S_SecondRecords, `RPz8_F3S_TwoRecords, `RPz8_F3S_TwoSegments, `RPz8_GExq_EventGood, `RPz8_RawK_RecordedHead, `RPz8_GExq_OuterGoodTwo, `RPz8_GExq_CallerRecord, `RPz8_F3S_ExactChildren, `RPz8_F3S_ChildLogs, `RPz8_F3S_NativeChildren, `RPz8_F3S_SdkDictionary, `RPz8_F3S_Dictionary, `RPz8_F3S_FirstBase, `RPz8_F3S_FirstPairLog, `RPz8_F3U_FirstCode, `RPz8_F3W_FirstLog, `RPz8_F3W_Runs, `RPz8_F3U_Slice, `RPz8_F3W_SourceLog, `RPz8_F3S_Silent, `RPz8_F3S_Residual, `RPz8_F3S_SecondProvenance, `RPz8_F3S_SecondRoot, `RPz8_F3S_SecondOnRun, `RPz8_F3U_ReaderCode, `RPz8_F3U_SecondCode, `RPz8_F3W_SecondLog, `RPz8_F3Q_BatchNative, `RPz8_F3N_BatchCode, `RPz8_F3N_BatchPrograms, `RPz8_F3Q_BatchSyntax, `RPz8_F3Q_SourceCurrentBatch, `RPz8_F3Q_FirstBatch, `RPz8_F3W_FirstBatch, `RPz8_F3Q_SourceBatch, `RPz8_F3Q_SecondBatch, `RPz8_F3W_SecondBatch, `RPz8_F3Q_CheckpointStage, `RPz8_F3Q_Variant, `RPz8_F3L_CheckpointNumeric, `RPz8_F3N_CheckpointLog, `RPz8_F3W_CheckpointLog, `RPz8_F3N_ModelBody, `RPz8_F3Q_BodyOnRun, `RPz8_F3R_PreparedCut, `RPz8_F3R_ConsPrepared, `RPz8_F3N_AuthenticatedTen, `RPz8_F3N_SourceInput, `RPz8_F3N_ConsSource, `RPz8_F3N_SameRun, `RPz8_F3N_SameRunTen, `RPz8_F3N_SameSecond, `RPz8_F3R_CheckpointNative, `RPz8_F3Q_PreparedCut, `RPz8_F3Q_ConsPrepared, `RPz8_F3R_PairBatches, `RPz8_F3Q_CheckpointLogOnRun, `RPz8_F3Q_CheckpointNative, `RPz8_F3R_PairCheckpointLog, `RPz8_F3N_SecondFinish, `RPz8_F3Q_PairBatches, `RPz8_F3R_PairFinish, `RPz8_F3R_PairModelFinish ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    if selected.contains owner then
      logInfo m!"RPZ8_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, _) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if selected.contains owner then
        let axs ← collectAxioms n
        logInfo m!"RPZ8_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ8_AUDIT_COMPLETE declarations={count} modules={selected.size}"
