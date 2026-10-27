import Lean
import RPz7_Hiq_DrvShape
import RPz7_Hiq_DecodedShape
import RPz7_Hiq_FirstShape
import RPz7_CPR_DataWriter
import RPz7_CPS_EntryFlags
import RPz7_CPS_BoundaryLoad
import RPz7_CPS_PhysicalKey
import RPz7_CPS_Ordinary
import RPz7_CPP_Oracle
import RPz7_CPP_Compatibility
import RPz7_CPP_OracleSource
import RPz7_CPP_Schedule
import RPz7_CPP_RunErasure
import RPz7_CPP_ProgramErasure
import RPz7_CPP_Atomic
import RPz7_CPP_AtomicLaws
import RPz7_CPP_AtomicSource
import RPz7_Hir_SelectedOrigin
import RPz7_Hir_CallSuccess
import RPz7_Hir_BirthSuffix
import RPz7_Hir_BirthCuts
import RPz7_Hir_LifetimeVersion
import RPz7_Hir_Recorded
import RPz7_Hir_RecordErasure
import RPz7_Hir_RecordNative
import RPz7_CPP_AtomicRecord
import RPz7_CPP_AtomicOrigin
import RPz7_CPP_Write
import RPz7_CPP_Protection
import RPz7_CPP_AtomicTrace
import RPz7_CPP_AtomicSchedule
import RPz7_CPP_AtomicRecorded
import RPz7_CPP_AtomicRecordNative
import RPz7_CPS_ParentStatus
import RPz7_CPG_Projection
import RPz7_CPG_RuntimeTrace
import RPz7_CPG_Game
import RPz7_CPH_Game
import RPz7_CPP_CallerSource
import RPz7_CPH_Result
import RPz7_CPG_Accepted
import RPz7_CPS_BankSource
import RPz7_CPS_BankRecorder
import RPz7_CPG_History
import RPz7_CPR_PhysicalResult
import RPz7_CPG_Result
import RPz7_FIs_Cons_Second
import RPz7_FIs_P2P_R5Close
import RPz7_RawJ_FirstTraceFields
import RPz7_RawJ_SecondTraceFields
import RPz7_RawJ_Cuts
import RPz7_RawJ_RecordCuts
import RPz7_P2P_Scheduled
import RPz7_SAP_Scheduled
import RPz7_P2P_D189
import RPz7_SAP_D189
import RPz7_P2P_Claims
import RPz7_SAP_Claims
import RPz7_P2P_Op3
import RPz7_SAP_Op3
import RPz7_P2P_Tx2
import RPz7_SAP_Tx2
import RPz7_P2P_Success
import RPz7_SAP_Success
import RPz7_P2P_Batches
import RPz7_SAP_Batches
import RPz7_P2P_Union
import RPz7_SAP_Union
import RPz7_P2P_SdkUnion
import RPz7_SAP_SdkUnion
import RPz7_P2P_SdkAccepted
import RPz7_SAP_SdkAccepted
import RPz7_P2P_CPhy
import RPz7_SAP_CPhy
import RPz7_P2P_Physical
import RPz7_SAP_Physical
import RPz7_P2P_FinishEffects
import RPz7_SAP_FinishEffects
import RPz7_P2P_NativePair
import RPz7_FIs_P2P_ResultSelected
import RPz7_SAP_NativePair
import RPz7_SAF_C_SAP_ResultSelected
import RPz7_SAF_C_Cons_FinishProof
import RPz7_FIs_P2P_PairSelected

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_Hiq_DrvShape, `RPz7_Hiq_DecodedShape, `RPz7_Hiq_FirstShape, `RPz7_CPR_DataWriter, `RPz7_CPS_EntryFlags, `RPz7_CPS_BoundaryLoad, `RPz7_CPS_PhysicalKey, `RPz7_CPS_Ordinary, `RPz7_CPP_Oracle, `RPz7_CPP_Compatibility, `RPz7_CPP_OracleSource, `RPz7_CPP_Schedule, `RPz7_CPP_RunErasure, `RPz7_CPP_ProgramErasure, `RPz7_CPP_Atomic, `RPz7_CPP_AtomicLaws, `RPz7_CPP_AtomicSource, `RPz7_Hir_SelectedOrigin, `RPz7_Hir_CallSuccess, `RPz7_Hir_BirthSuffix, `RPz7_Hir_BirthCuts, `RPz7_Hir_LifetimeVersion, `RPz7_Hir_Recorded, `RPz7_Hir_RecordErasure, `RPz7_Hir_RecordNative, `RPz7_CPP_AtomicRecord, `RPz7_CPP_AtomicOrigin, `RPz7_CPP_Write, `RPz7_CPP_Protection, `RPz7_CPP_AtomicTrace, `RPz7_CPP_AtomicSchedule, `RPz7_CPP_AtomicRecorded, `RPz7_CPP_AtomicRecordNative, `RPz7_CPS_ParentStatus, `RPz7_CPG_Projection, `RPz7_CPG_RuntimeTrace, `RPz7_CPG_Game, `RPz7_CPH_Game, `RPz7_CPP_CallerSource, `RPz7_CPH_Result, `RPz7_CPG_Accepted, `RPz7_CPS_BankSource, `RPz7_CPS_BankRecorder, `RPz7_CPG_History, `RPz7_CPR_PhysicalResult, `RPz7_CPG_Result, `RPz7_FIs_Cons_Second, `RPz7_FIs_P2P_R5Close, `RPz7_RawJ_FirstTraceFields, `RPz7_RawJ_SecondTraceFields, `RPz7_RawJ_Cuts, `RPz7_RawJ_RecordCuts, `RPz7_P2P_Scheduled, `RPz7_SAP_Scheduled, `RPz7_P2P_D189, `RPz7_SAP_D189, `RPz7_P2P_Claims, `RPz7_SAP_Claims, `RPz7_P2P_Op3, `RPz7_SAP_Op3, `RPz7_P2P_Tx2, `RPz7_SAP_Tx2, `RPz7_P2P_Success, `RPz7_SAP_Success, `RPz7_P2P_Batches, `RPz7_SAP_Batches, `RPz7_P2P_Union, `RPz7_SAP_Union, `RPz7_P2P_SdkUnion, `RPz7_SAP_SdkUnion, `RPz7_P2P_SdkAccepted, `RPz7_SAP_SdkAccepted, `RPz7_P2P_CPhy, `RPz7_SAP_CPhy, `RPz7_P2P_Physical, `RPz7_SAP_Physical, `RPz7_P2P_FinishEffects, `RPz7_SAP_FinishEffects, `RPz7_P2P_NativePair, `RPz7_FIs_P2P_ResultSelected, `RPz7_SAP_NativePair, `RPz7_SAF_C_SAP_ResultSelected, `RPz7_SAF_C_Cons_FinishProof, `RPz7_FIs_P2P_PairSelected ]
  let phaseOwners : Array Name := #[ `RPz7_S1SemanticPrefixModelV1, `RPz7_S1SemanticFinishModelV1, `RPz7_S1SemanticFinishBoundsV1, `RPz7_ClaimsUnrolledFinish, `RPz7_S1SemanticVerifyReachabilityV1, `RPz7_S1SemanticFinishRootsV1, `RPz7_S1AcceptedSemanticNumericV1, `RPz7_S1AcceptedChallengesNumericV1, `RPz7_S1SemanticCodeFinishV1, `RPz7_S1SemanticCodeVerifyV1, `RPz7_S1SemanticCodeFinishExactV1, `RPz7_S1SemanticCodeVerifyExactV1, `RPz7_GExp_FinishAssociation, `RPz7_GExp_VerifyAssociation, `RPz7_S1SemanticBudgetV1, `RPz7_AuS1_Semantic3, `RPz7_F3V_SemanticFinish, `RPz7_F3V_SemanticVerify, `RPz7_RawJ_VerifyRead, `RPz7_RawK_VerifyHead, `RPz7_F3U_VerifyHead ]
  for i in [:env.header.modules.size] do
    let owner := env.header.modules[i]!.module
    let data := env.header.moduleData[i]!
    logInfo m!"RPZ7_IMPORTS {(Json.mkObj [("module", toJson owner.toString), ("imports", toJson (data.imports.map (·.module.toString)))]).compress}"
  let mut count : Nat := 0
  for (n, c) in env.toKernelEnv.constants.toList do
    if let some mi := env.getModuleIdxFor? n then
      let owner := env.header.modules[mi.toNat]!.module
      if c.isAxiom then
        logInfo m!"RPZ7_AXIOM {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString)]).compress}"
      if selected.contains owner then
        let debugPrefixes := #["AspisR1RecordParser.r1_wire.Error.Insts.CoreFmtDebug", "AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug"]
        let refs := c.type.getUsedConstants ++ (((c.value? true).map (fun e => e.getUsedConstants)).getD #[])
        for ref in refs do
          if debugPrefixes.any (fun p => ref.toString == p || ref.toString.startsWith (p ++ ".")) then
            logInfo m!"RPZ7_DEBUG_REF {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("reference", toJson ref.toString)]).compress}"
        if phaseOwners.contains owner || n.toString.startsWith "RPz7_PhaseIso" || n.toString == "AspisR1.Rc10_Top.deployed" then
          logInfo m!"RPZ7_KERNEL_TYPE {(Json.mkObj [("name", toJson n.toString), ("type", toJson (repr c.type).pretty)]).compress}"
        let axs ← collectAxioms n
        logInfo m!"RPZ7_DECL {(Json.mkObj [("module", toJson owner.toString), ("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))]).compress}"
        elabCommand (← `(#print axioms $(mkIdent n)))
        count := count + 1
  logInfo m!"RPZ7_AUDIT_COMPLETE declarations={count} modules={selected.size}"
