import Lean
import RPz8_F3V_StageDictionary
import RPz8_F3V_StageBatch
import RPz8_F3V_SecondCode
import RPz8_F3V_SecondComplete
import RPz8_F3V_AllWorldPair
import RPz8_F3V_FirstSlots
import RPz8_F3V_Parser
import RPz8_F3V_FirstRun
import RPz8_F3V_Decoded
import RPz8_F3V_PublicModel
import RPz8_F3V_Public
import RPz8_F3V_PreparedModel
import RPz8_F3V_SourceInput
import RPz8_F3V_IdealBackend
import RPz8_F3V_AllWorldInput
import RPz8_F3V_Install
import RPz8_F3K_CodeBind
import RPz8_F3K_CodePure
import RPz8_F3Q_PreparePure
import RPz8_F3R_Result
import RPz8_F3R_Try
import RPz8_RawJ_MapSuccess
import RPz8_RawJ_DigestRead
import RPz8_RawJ_InitRead
import RPz8_RawJ_PublicRead
import RPz8_RawJ_VerifyRead
import RPz8_RawJ_SemanticRead
import RPz8_F3R_PrepareBuffers
import RPz8_F3R_BothBuffers
import RPz8_F3R_Pure
import RPz8_F3R_FinishTailCode
import RPz8_F3R_FinishTail
import RPz8_F3R_FinishSplit
import RPz8_F3R_VerifySplit
import RPz8_F3J_SourceBlock
import RPz8_F3J_SourceBlockValue
import RPz8_F3J_ValidatedLog
import RPz8_F3R_SemanticStep
import RPz8_F3R_SemanticChain
import RPz8_F3R_Begin13
import RPz8_F3R_ArrayAccess
import RPz8_F3R_Begin9
import RPz8_F3R_Begin5
import RPz8_F3R_Begin
import RPz8_F3R_TraceSplit
import RPz8_F3R_TraceHead
import RPz8_F3R_BeginTrace
import RPz8_F3R_RoundStep
import RPz8_F3R_RoundState
import RPz8_F3R_Rounds
import RPz8_F3R_RoundsTrace
import RPz8_F3R_PublicLog
import RPz8_F3R_TraceAppend
import RPz8_F3R_VerifyLog
import RPz8_F3R_TraceUnique
import RPz8_F3R_InitUnique
import RPz8_F3R_SemanticOnTrace
import RPz8_F3Q_PrepareMap
import RPz8_F3R_JoinedRun
import RPz8_F3Q_HashBind
import RPz8_F3K_PrepareLog
import RPz8_F3Q_OpeningSourceLog
import RPz8_F3V_PreparedExact
import RPz8_F3R_PreparedSource
import RPz8_F3R_ModelSchedule
import RPz8_F3R_Admission
import RPz8_F3V_PreparedAdmitted
import RPz8_F3V_PreparedFacts
import RPz8_F3V_AllWorldPrepared
import RPz8_F3V_SecondSlots
import RPz8_F3V_AllWorldNative
import RPz8_F3V_SecondRun
import RPz8_F3V_RunEvidence
import RPz8_F3V_DigestCompatibility
import RPz8_F3V_EvidenceCalls
import RPz8_F3V_FirstBatchModel
import RPz8_F3V_WriterCall
import RPz8_F3V_SecondBatchModel
import RPz8_F3V_Authenticated
import RPz8_F3N_Ten
import RPz8_F3V_Ten
import RPz8_F3V_CheckpointOracle
import RPz8_F3V_WriterModel
import RPz8_F3N_TenInput
import RPz8_F3V_Checkpoint
import RPz8_FGl_Finish
import RPz8_FGl_FinishProof
import RPz8_FIp_RunFinish
import RPz8_F3N_ReaderNumeric
import RPz8_F3Y_PreparedScalars
import RPz8_F3Y_FinishFields
import RPz8_F3R_Finish
import RPz8_F3S_FinishContinuation
import RPz8_F3S_ModelLog
import RPz8_F3S_InputAtSecond
import RPz8_F3S_ModelAcceptance
import RPz8_F3S_AcceptanceValues
import RPz8_F3T_Leaves
import RPz8_F3Y_FinishLeaves
import RPz8_FIn_Derived
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz8_F3V_StageDictionary, `RPz8_F3V_StageBatch, `RPz8_F3V_SecondCode, `RPz8_F3V_SecondComplete, `RPz8_F3V_AllWorldPair, `RPz8_F3V_FirstSlots, `RPz8_F3V_Parser, `RPz8_F3V_FirstRun, `RPz8_F3V_Decoded, `RPz8_F3V_PublicModel, `RPz8_F3V_Public, `RPz8_F3V_PreparedModel, `RPz8_F3V_SourceInput, `RPz8_F3V_IdealBackend, `RPz8_F3V_AllWorldInput, `RPz8_F3V_Install, `RPz8_F3K_CodeBind, `RPz8_F3K_CodePure, `RPz8_F3Q_PreparePure, `RPz8_F3R_Result, `RPz8_F3R_Try, `RPz8_RawJ_MapSuccess, `RPz8_RawJ_DigestRead, `RPz8_RawJ_InitRead, `RPz8_RawJ_PublicRead, `RPz8_RawJ_VerifyRead, `RPz8_RawJ_SemanticRead, `RPz8_F3R_PrepareBuffers, `RPz8_F3R_BothBuffers, `RPz8_F3R_Pure, `RPz8_F3R_FinishTailCode, `RPz8_F3R_FinishTail, `RPz8_F3R_FinishSplit, `RPz8_F3R_VerifySplit, `RPz8_F3J_SourceBlock, `RPz8_F3J_SourceBlockValue, `RPz8_F3J_ValidatedLog, `RPz8_F3R_SemanticStep, `RPz8_F3R_SemanticChain, `RPz8_F3R_Begin13, `RPz8_F3R_ArrayAccess, `RPz8_F3R_Begin9, `RPz8_F3R_Begin5, `RPz8_F3R_Begin, `RPz8_F3R_TraceSplit, `RPz8_F3R_TraceHead, `RPz8_F3R_BeginTrace, `RPz8_F3R_RoundStep, `RPz8_F3R_RoundState, `RPz8_F3R_Rounds, `RPz8_F3R_RoundsTrace, `RPz8_F3R_PublicLog, `RPz8_F3R_TraceAppend, `RPz8_F3R_VerifyLog, `RPz8_F3R_TraceUnique, `RPz8_F3R_InitUnique, `RPz8_F3R_SemanticOnTrace, `RPz8_F3Q_PrepareMap, `RPz8_F3R_JoinedRun, `RPz8_F3Q_HashBind, `RPz8_F3K_PrepareLog, `RPz8_F3Q_OpeningSourceLog, `RPz8_F3V_PreparedExact, `RPz8_F3R_PreparedSource, `RPz8_F3R_ModelSchedule, `RPz8_F3R_Admission, `RPz8_F3V_PreparedAdmitted, `RPz8_F3V_PreparedFacts, `RPz8_F3V_AllWorldPrepared, `RPz8_F3V_SecondSlots, `RPz8_F3V_AllWorldNative, `RPz8_F3V_SecondRun, `RPz8_F3V_RunEvidence, `RPz8_F3V_DigestCompatibility, `RPz8_F3V_EvidenceCalls, `RPz8_F3V_FirstBatchModel, `RPz8_F3V_WriterCall, `RPz8_F3V_SecondBatchModel, `RPz8_F3V_Authenticated, `RPz8_F3N_Ten, `RPz8_F3V_Ten, `RPz8_F3V_CheckpointOracle, `RPz8_F3V_WriterModel, `RPz8_F3N_TenInput, `RPz8_F3V_Checkpoint, `RPz8_FGl_Finish, `RPz8_FGl_FinishProof, `RPz8_FIp_RunFinish, `RPz8_F3N_ReaderNumeric, `RPz8_F3Y_PreparedScalars, `RPz8_F3Y_FinishFields, `RPz8_F3R_Finish, `RPz8_F3S_FinishContinuation, `RPz8_F3S_ModelLog, `RPz8_F3S_InputAtSecond, `RPz8_F3S_ModelAcceptance, `RPz8_F3S_AcceptanceValues, `RPz8_F3T_Leaves, `RPz8_F3Y_FinishLeaves, `RPz8_FIn_Derived ]
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
