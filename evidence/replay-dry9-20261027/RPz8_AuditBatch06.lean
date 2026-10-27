import Lean
import RPz8_SCI_Recovery
import RPz8_ARQ_ModelAccepted
import RPz8_SCG_RawRecovery
import RPz8_ARQ_ObservedRecovery
import RPz8_ARQ_LowerTrace
import RPz8_SCG_OuterLog
import RPz8_SCG_BatchBody
import RPz8_SCG_BatchDictionary
import RPz8_SCG_BatchCode
import RPz8_SCG_FirstCode
import RPz8_ARQ_FirstTrace
import RPz8_ARQ_CallFacts
import RPz8_ARQ_FirstOperands
import RPz8_ARQ_FirstOperandsBytes
import RPz8_ARQ_FirstBytes
import RPz8_ARQ_FirstBody
import RPz8_ARQ_ChildDigest
import RPz8_ARQ_FirstIdeal
import RPz8_ARQ_IdealFirstRun
import RPz8_ARQ_DecodeAlignment
import RPz8_ARQ_ActualFirst
import RPz8_ARQ_FirstMatches
import RPz8_ARQ_PreparationPrefix
import RPz8_ARQ_PhysicalSampler
import RPz8_ARQ_Canonical
import RPz8_ARQ_AccountPrefix
import RPz8_ARQ_AccountPreparation
import RPz8_ARP_Interface
import RPz8_ARQ_Observer
import RPz8_ARQ_QueryProjection
import RPz8_ARQ_SavedQueries
import RPz8_SCE_CompleteSubmission
import RPz8_SCE_AccountBound
import RPz8_RPx_ChargeBudget
import RPz8_SCF_Charge
import RPz8_ARQ_Charge
import RPz8_ARQ_RecoveryBranch
import RPz8_ARQ_SourceBranch
import RPz8_SCG_NativeAccount
import RPz8_SCG_Selection
import RPz8_SCG_Recorder
import RPz8_SCG_SharedNative
import RPz8_ARQ_ByteSourceAccepts
import RPz8_ARQ_SourceAlternative
import RPz8_ARQ_NativeReplies
import RPz8_ARQ_Transport
import RPz8_SCF_Domination
import RPz8_SCE_FailureZero
import RPz8_SCE_AccountMass
import RPz8_SCF_RequiredTransport
import RPz8_ARQ_WorldSupport
import RPz8_ARS_Coverage
import RPz8_ARU_Support
import RPz8_ARU_Replies
import RPz8_ARU_WrapperSource
import RPz8_ARU_SourceResults
import RPz8_ART_PartialProgram
import RPz8_ART_QueryAgreement
import RPz8_ART_PartialExact
import RPz8_ARS_NativeCost
import RPz8_ARS_NativeOutcome
import RPz8_ART_PartialAccount
import RPz8_ART_WrapperExact
import RPz8_ARV_FirstPartial
import RPz8_ARW_Induced
import RPz8_ART_Coverage
import RPz8_RPx_RejectMass
import RPz8_ART_Runtime
import RPz8_ART_FirstProjection
import RPz8_ART_AcceptedBridge
import RPz8_ART_WrapperAccepted
import RPz8_ART_AccountAccepted
import RPz8_ART_PhysicalView
import RPz8_ARU_DecodedOrigin
import RPz8_ARU_CutsOrigin
import RPz8_ARU_SelectorPure
import RPz8_ARU_Selector
import RPz8_ARU_Header
import RPz8_SCH_Oracle
import RPz8_ARU_WriterHeader
import RPz8_ARU_WriterReached
import RPz8_SCH_FirstChild
import RPz8_ARU_FirstHeader
import RPz8_ARU_ReaderHeader
import RPz8_ARU_ReaderReached
import RPz8_SCG_SecondCode
import RPz8_SCH_SecondChild
import RPz8_ARU_SecondHeader
import RPz8_ARU_ByteMatch
import RPz8_CPH_Top
import RPz8_SCJ_Checkpoint
import RPz8_SCJ_NativeLoaded
import RPz8_ARQ_BankCut
import RPz8_SCH_IdealSplit
import RPz8_SCH_IdealFirst
import RPz8_SCH_IdealSecond
import RPz8_SCH_DriverAcceptance
import RPz8_ARU_PartialAccepted
import RPz8_ART_PrefixCoupling
import RPz8_ART_AdversaryWork
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array Name := #[ `RPz8_SCI_Recovery, `RPz8_ARQ_ModelAccepted, `RPz8_SCG_RawRecovery, `RPz8_ARQ_ObservedRecovery, `RPz8_ARQ_LowerTrace, `RPz8_SCG_OuterLog, `RPz8_SCG_BatchBody, `RPz8_SCG_BatchDictionary, `RPz8_SCG_BatchCode, `RPz8_SCG_FirstCode, `RPz8_ARQ_FirstTrace, `RPz8_ARQ_CallFacts, `RPz8_ARQ_FirstOperands, `RPz8_ARQ_FirstOperandsBytes, `RPz8_ARQ_FirstBytes, `RPz8_ARQ_FirstBody, `RPz8_ARQ_ChildDigest, `RPz8_ARQ_FirstIdeal, `RPz8_ARQ_IdealFirstRun, `RPz8_ARQ_DecodeAlignment, `RPz8_ARQ_ActualFirst, `RPz8_ARQ_FirstMatches, `RPz8_ARQ_PreparationPrefix, `RPz8_ARQ_PhysicalSampler, `RPz8_ARQ_Canonical, `RPz8_ARQ_AccountPrefix, `RPz8_ARQ_AccountPreparation, `RPz8_ARP_Interface, `RPz8_ARQ_Observer, `RPz8_ARQ_QueryProjection, `RPz8_ARQ_SavedQueries, `RPz8_SCE_CompleteSubmission, `RPz8_SCE_AccountBound, `RPz8_RPx_ChargeBudget, `RPz8_SCF_Charge, `RPz8_ARQ_Charge, `RPz8_ARQ_RecoveryBranch, `RPz8_ARQ_SourceBranch, `RPz8_SCG_NativeAccount, `RPz8_SCG_Selection, `RPz8_SCG_Recorder, `RPz8_SCG_SharedNative, `RPz8_ARQ_ByteSourceAccepts, `RPz8_ARQ_SourceAlternative, `RPz8_ARQ_NativeReplies, `RPz8_ARQ_Transport, `RPz8_SCF_Domination, `RPz8_SCE_FailureZero, `RPz8_SCE_AccountMass, `RPz8_SCF_RequiredTransport, `RPz8_ARQ_WorldSupport, `RPz8_ARS_Coverage, `RPz8_ARU_Support, `RPz8_ARU_Replies, `RPz8_ARU_WrapperSource, `RPz8_ARU_SourceResults, `RPz8_ART_PartialProgram, `RPz8_ART_QueryAgreement, `RPz8_ART_PartialExact, `RPz8_ARS_NativeCost, `RPz8_ARS_NativeOutcome, `RPz8_ART_PartialAccount, `RPz8_ART_WrapperExact, `RPz8_ARV_FirstPartial, `RPz8_ARW_Induced, `RPz8_ART_Coverage, `RPz8_RPx_RejectMass, `RPz8_ART_Runtime, `RPz8_ART_FirstProjection, `RPz8_ART_AcceptedBridge, `RPz8_ART_WrapperAccepted, `RPz8_ART_AccountAccepted, `RPz8_ART_PhysicalView, `RPz8_ARU_DecodedOrigin, `RPz8_ARU_CutsOrigin, `RPz8_ARU_SelectorPure, `RPz8_ARU_Selector, `RPz8_ARU_Header, `RPz8_SCH_Oracle, `RPz8_ARU_WriterHeader, `RPz8_ARU_WriterReached, `RPz8_SCH_FirstChild, `RPz8_ARU_FirstHeader, `RPz8_ARU_ReaderHeader, `RPz8_ARU_ReaderReached, `RPz8_SCG_SecondCode, `RPz8_SCH_SecondChild, `RPz8_ARU_SecondHeader, `RPz8_ARU_ByteMatch, `RPz8_CPH_Top, `RPz8_SCJ_Checkpoint, `RPz8_SCJ_NativeLoaded, `RPz8_ARQ_BankCut, `RPz8_SCH_IdealSplit, `RPz8_SCH_IdealFirst, `RPz8_SCH_IdealSecond, `RPz8_SCH_DriverAcceptance, `RPz8_ARU_PartialAccepted, `RPz8_ART_PrefixCoupling, `RPz8_ART_AdversaryWork ]
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
