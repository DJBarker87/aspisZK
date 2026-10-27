import Lean
import RPz7_GExq_OuterGoodMap
import RPz7_GExq_OuterGoodBinds
import RPz7_GExq_OuterGoodStage1
import RPz7_GExq_OuterGoodStage2
import RPz7_GExq_OuterRecord
import RPz7_GExq_RecordTrace
import RPz7_GExq_Caller
import RPz7_GExq_WrapperCode
import RPz7_GExq_InstalledWrapper
import RPz7_GExq_WrapperAccepted
import RPz7_GExq_AccountExperiment
import RPz7_Hiq_ByteSelection
import RPz7_Hiq_Suffix
import RPz7_Hist_AuditQueries
import RPz7_Hist_ChargedBinding
import RPz7_Hist_PairExperiment
import RPz7_Hiq_Association
import RPz7_GExq_Credit
import RPz7_GExq_CreditTactic
import RPz7_GExq_BatchCredit
import RPz7_GExq_BatchLoop
import RPz7_GExq_BatchTree
import RPz7_GExq_BatchBudget
import RPz7_GExq_FirstBudget
import RPz7_GExq_SecondBudget
import RPz7_GExq_GlobalBudget
import RPz7_RawJ_OuterBudget
import RPz7_RawJ_OuterHelpers
import RPz7_RawJ_FirstOuter
import RPz7_RawJ_SecondOuter
import RPz7_RawJ_FirstBudget
import RPz7_RawJ_SecondBudget
import RPz7_RawJ_ChildBudget
import RPz7_RawJ_CallerBudget
import RPz7_RawJ_WrapperBudget
import RPz7_RawJ_InstalledBudget
import RPz7_RawJ_AccountBudget
import RPz7_RawJ_CollisionBudget
import RPz7_Hist_ByteExperiment
import RPz7_Hist_JointCharge
import RPz7_Hiq_AccountAudit
import RPz7_Hiq_JointBinding
import RPz7_GExq_AccountAccepted
import RPz7_Hiq_AccountBinding
import RPz7_Hiq_DrvExperiment
import RPz7_Hir_Call
import RPz7_CPP_Invocation
import RPz7_CPP_Gates
import RPz7_Hir_CallSource
import RPz7_Hir_CallClassify
import RPz7_CPP_Classify
import RPz7_Hir_Schedule
import RPz7_Hir_ScheduleTrace
import RPz7_Hir_ScheduleSource
import RPz7_Hir_CallLog
import RPz7_Hir_ScheduleLog
import RPz7_Hir_Choice
import RPz7_Hir_FirstChoice
import RPz7_Hir_ChoiceLog
import RPz7_Hir_Factory
import RPz7_Hir_FactoryLoad
import RPz7_Hir_FactoryCharge
import RPz7_Hir_ProvenanceModel
import RPz7_Hir_Zero
import RPz7_Hir_ForeignBack
import RPz7_Hir_CallBirth
import RPz7_Hir_ScheduleOrigin
import RPz7_Hir_GenesisOrigin
import RPz7_Hir_ReaderMarker
import RPz7_Hir_InstalledReader
import RPz7_Hir_ReaderEntry
import RPz7_CPP_BankSourceLoad
import RPz7_CPP_BankState
import RPz7_CPR_Persistence
import RPz7_CPR_DataPersistence
import RPz7_CPP_BankFrame
import RPz7_CPP_BankHistory
import RPz7_CPP_BankEvents
import RPz7_CPP_BankBinding
import RPz7_CPR_AtomicBank
import RPz7_CPR_DataBinding
import RPz7_CPR_RuntimeBinding
import RPz7_CPR_SourceBank
import RPz7_Hist_SdkShape

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz7_GExq_OuterGoodMap, `RPz7_GExq_OuterGoodBinds, `RPz7_GExq_OuterGoodStage1, `RPz7_GExq_OuterGoodStage2, `RPz7_GExq_OuterRecord, `RPz7_GExq_RecordTrace, `RPz7_GExq_Caller, `RPz7_GExq_WrapperCode, `RPz7_GExq_InstalledWrapper, `RPz7_GExq_WrapperAccepted, `RPz7_GExq_AccountExperiment, `RPz7_Hiq_ByteSelection, `RPz7_Hiq_Suffix, `RPz7_Hist_AuditQueries, `RPz7_Hist_ChargedBinding, `RPz7_Hist_PairExperiment, `RPz7_Hiq_Association, `RPz7_GExq_Credit, `RPz7_GExq_CreditTactic, `RPz7_GExq_BatchCredit, `RPz7_GExq_BatchLoop, `RPz7_GExq_BatchTree, `RPz7_GExq_BatchBudget, `RPz7_GExq_FirstBudget, `RPz7_GExq_SecondBudget, `RPz7_GExq_GlobalBudget, `RPz7_RawJ_OuterBudget, `RPz7_RawJ_OuterHelpers, `RPz7_RawJ_FirstOuter, `RPz7_RawJ_SecondOuter, `RPz7_RawJ_FirstBudget, `RPz7_RawJ_SecondBudget, `RPz7_RawJ_ChildBudget, `RPz7_RawJ_CallerBudget, `RPz7_RawJ_WrapperBudget, `RPz7_RawJ_InstalledBudget, `RPz7_RawJ_AccountBudget, `RPz7_RawJ_CollisionBudget, `RPz7_Hist_ByteExperiment, `RPz7_Hist_JointCharge, `RPz7_Hiq_AccountAudit, `RPz7_Hiq_JointBinding, `RPz7_GExq_AccountAccepted, `RPz7_Hiq_AccountBinding, `RPz7_Hiq_DrvExperiment, `RPz7_Hir_Call, `RPz7_CPP_Invocation, `RPz7_CPP_Gates, `RPz7_Hir_CallSource, `RPz7_Hir_CallClassify, `RPz7_CPP_Classify, `RPz7_Hir_Schedule, `RPz7_Hir_ScheduleTrace, `RPz7_Hir_ScheduleSource, `RPz7_Hir_CallLog, `RPz7_Hir_ScheduleLog, `RPz7_Hir_Choice, `RPz7_Hir_FirstChoice, `RPz7_Hir_ChoiceLog, `RPz7_Hir_Factory, `RPz7_Hir_FactoryLoad, `RPz7_Hir_FactoryCharge, `RPz7_Hir_ProvenanceModel, `RPz7_Hir_Zero, `RPz7_Hir_ForeignBack, `RPz7_Hir_CallBirth, `RPz7_Hir_ScheduleOrigin, `RPz7_Hir_GenesisOrigin, `RPz7_Hir_ReaderMarker, `RPz7_Hir_InstalledReader, `RPz7_Hir_ReaderEntry, `RPz7_CPP_BankSourceLoad, `RPz7_CPP_BankState, `RPz7_CPR_Persistence, `RPz7_CPR_DataPersistence, `RPz7_CPP_BankFrame, `RPz7_CPP_BankHistory, `RPz7_CPP_BankEvents, `RPz7_CPP_BankBinding, `RPz7_CPR_AtomicBank, `RPz7_CPR_DataBinding, `RPz7_CPR_RuntimeBinding, `RPz7_CPR_SourceBank, `RPz7_Hist_SdkShape ]
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
