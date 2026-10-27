import SCH_AcceptedSources
import SCH_AccountCuts
import SCH_AccountDecoded
import SCH_AccountDriver
import SCH_AccountLog
import SCH_AccountSubmission
import SCH_CheckNames
import SCH_ChildUpdate
import SCH_CollisionAppend
import SCH_CollisionInsert
import SCH_CollisionInventory
import SCH_CollisionKnownSuffix
import SCH_DecodeAlign
import SCH_DecodedCuts
import SCH_DigestAlign
import SCH_DriverAcceptance
import SCH_EventKnownSuffix
import SCH_FirstChild
import SCH_GameSelection
import SCH_IdealFirst
import SCH_IdealSdk
import SCH_IdealSdkInvoke
import SCH_IdealSecond
import SCH_IdealSplit
import SCH_InspectPure
import SCH_InstalledStage
import SCH_Ledger01
import SCH_Ledger02
import SCH_Ledger03
import SCH_Ledger04
import SCH_Ledger05
import SCH_Ledger06
import SCH_Ledger07
import SCH_Ledger08
import SCH_Ledger09
import SCH_Ledger10
import SCH_Ledger11
import SCH_Lower
import SCH_Nonvacuity
import SCH_Oracle
import SCH_OracleErase
import SCH_OracleQuantifier
import SCH_OuterFirstIdentity
import SCH_OuterIdealLog
import SCH_OuterSecondIdentity
import SCH_OuterTrace
import SCH_RangeAt
import SCH_RecorderProjection
import SCH_RootAudit
import SCH_SdkPure
import SCH_SdkSecond
import SCH_SecondChild
import SCH_SecondPure
import SCH_SourceCuts
import SCH_SourceFirst
import SCH_SourceSecond
import SCH_StageAlign
import SCH_TableAfter
import SCH_TableFixed
import SCH_TraceExists
import SCH_UpdateAuthenticate
import SCH_UpdatePure
import SCH_UpdateRegistry
import SCH_UpdateValidate
import SCH_WrapperFirst
import SCH_WrapperSecond

#print axioms AspisR1.SCH_AcceptedSources.accepted
#print axioms AspisR1.SCH_AccountCuts.accepted
#print axioms AspisR1.SCH_AccountDecoded.accepted
#print axioms AspisR1.SCH_AccountDriver.accepted
#print axioms AspisR1.SCH_AccountLog.chronological
#print axioms AspisR1.SCH_AccountSubmission.accepted
#print axioms AspisR1.SCH_ChildUpdate.original
#print axioms AspisR1.SCH_CollisionAppend.append
#print axioms AspisR1.SCH_CollisionAppend.cached
#print axioms AspisR1.SCH_CollisionInsert.table_append
#print axioms AspisR1.SCH_CollisionInsert.same
#print axioms AspisR1.SCH_CollisionKnownSuffix.same
#print axioms AspisR1.SCH_DecodeAlign.update
#print axioms AspisR1.SCH_DecodeAlign.installed
#print axioms AspisR1.SCH_DecodedCuts.pair
#print axioms AspisR1.SCH_DigestAlign.source
#print axioms AspisR1.SCH_DriverAcceptance.accepted
#print axioms AspisR1.SCH_EventKnownSuffix.same
#print axioms AspisR1.SCH_FirstChild.accepted
#print axioms AspisR1.SCH_GameSelection.fixed_first
#print axioms AspisR1.SCH_GameSelection.adaptive_entries
#print axioms AspisR1.SCH_IdealFirst.accepted
#print axioms AspisR1.SCH_IdealSdkInvoke.invoke
#print axioms AspisR1.SCH_IdealSecond.accepted
#print axioms AspisR1.SCH_IdealSplit.split
#print axioms AspisR1.SCH_InstalledStage.same
#print axioms AspisR1.SCH_Lower.result
#print axioms AspisR1.SCH_Nonvacuity.interpretation
#print axioms AspisR1.SCH_Oracle.evaluation
#print axioms AspisR1.SCH_OracleErase.result
#print axioms AspisR1.SCH_OracleQuantifier.fixed_world
#print axioms AspisR1.SCH_OracleQuantifier.not_all_worlds
#print axioms AspisR1.SCH_OuterFirstIdentity.code
#print axioms AspisR1.SCH_OuterIdealLog.flatten
#print axioms AspisR1.SCH_OuterSecondIdentity.code
#print axioms AspisR1.SCH_OuterTrace.accepted
#print axioms AspisR1.SCH_RangeAt.same
#print axioms AspisR1.SCH_RecorderProjection.logs
#print axioms AspisR1.SCH_RecorderProjection.event
#print axioms AspisR1.SCH_SdkPure.distinct
#print axioms AspisR1.SCH_SdkPure.checkpoint
#print axioms AspisR1.SCH_SdkPure.data
#print axioms AspisR1.SCH_SdkPure.prefix_bytes
#print axioms AspisR1.SCH_SdkPure.digest
#print axioms AspisR1.SCH_SdkPure.observer
#print axioms AspisR1.SCH_SdkSecond.validation
#print axioms AspisR1.SCH_SdkSecond.range
#print axioms AspisR1.SCH_SdkSecond.option_eq
#print axioms AspisR1.SCH_SdkSecond.statement_bytes
#print axioms AspisR1.SCH_SecondChild.accepted
#print axioms AspisR1.SCH_SecondPure.full_range
#print axioms AspisR1.SCH_SecondPure.option_eq
#print axioms AspisR1.SCH_SecondPure.readonly
#print axioms AspisR1.SCH_SourceCuts.pair
#print axioms AspisR1.SCH_SourceFirst.accepted
#print axioms AspisR1.SCH_SourceSecond.accepted
#print axioms AspisR1.SCH_StageAlign.library
#print axioms AspisR1.SCH_TableAfter.put_keeps
#print axioms AspisR1.SCH_TableAfter.keeps
#print axioms AspisR1.SCH_TableAfter.read
#print axioms AspisR1.SCH_TableFixed.put_same
#print axioms AspisR1.SCH_TableFixed.after_same
#print axioms AspisR1.SCH_TraceExists.accepted
#print axioms AspisR1.SCH_UpdateAuthenticate.same
#print axioms AspisR1.SCH_UpdatePure.data
#print axioms AspisR1.SCH_UpdatePure.checkpoint
#print axioms AspisR1.SCH_UpdatePure.distinct
#print axioms AspisR1.SCH_UpdatePure.pubkey
#print axioms AspisR1.SCH_UpdateRegistry.same
#print axioms AspisR1.SCH_UpdateValidate.same
#print axioms AspisR1.SCH_WrapperFirst.body
#print axioms AspisR1.SCH_WrapperSecond.body

-- Complete statements: deepTerms avoids the default printer's omitted tails.
set_option pp.fullNames true
set_option pp.deepTerms true
set_option format.width 120
#check @AspisR1.Rc7_Top.deployed
#check @AspisR1.SCH_AccountDriver.accepted
#check @AspisR1.SCH_AccountDecoded.accepted
