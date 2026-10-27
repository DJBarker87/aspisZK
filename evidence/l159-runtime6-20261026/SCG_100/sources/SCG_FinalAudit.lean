import SCG_AcceptedExecution
import SCG_AcceptedPair
import SCG_AcceptedShape
import SCG_AuditAllocator
import SCG_AuditBank
import SCG_AuditBasisArithmetic
import SCG_AuditChildren
import SCG_AuditCleanGuard
import SCG_AuditCompatibility
import SCG_AuditConfiguration
import SCG_AuditContinuation
import SCG_AuditCuts
import SCG_AuditEntry
import SCG_AuditEvent
import SCG_AuditExtraction
import SCG_AuditFinish
import SCG_AuditFinishLaws
import SCG_AuditGame
import SCG_AuditGeometryDomain
import SCG_AuditGlobalOwners
import SCG_AuditHistory
import SCG_AuditInstallation
import SCG_AuditLiteral
import SCG_AuditM31Opening
import SCG_AuditNP6
import SCG_AuditNativeDirection
import SCG_AuditNonvacuity
import SCG_AuditOldCarriers
import SCG_AuditOracle
import SCG_AuditOtherCones
import SCG_AuditP6Accepted
import SCG_AuditP6Boundary
import SCG_AuditP6Discharge
import SCG_AuditP6Full
import SCG_AuditP6SameCuts
import SCG_AuditParserEncoding
import SCG_AuditParserEntry
import SCG_AuditParserGates
import SCG_AuditParserPacket
import SCG_AuditPersistence
import SCG_AuditPhysical
import SCG_AuditPrimitive
import SCG_AuditProjection
import SCG_AuditRawCarriers
import SCG_AuditRawJoin
import SCG_AuditRecorderCarriers
import SCG_AuditRecoveryInputs
import SCG_AuditResult
import SCG_AuditResultBinding
import SCG_AuditRoot
import SCG_AuditSdk
import SCG_AuditSharedSelection
import SCG_AuditSlots
import SCG_AuditStd
import SCG_BatchBody
import SCG_BatchCode
import SCG_BatchDictionary
import SCG_Charge
import SCG_CodeMap
import SCG_Composition
import SCG_FirstCode
import SCG_FirstTraceLog
import SCG_Interfaces
import SCG_NativeAccount
import SCG_Nonvacuity
import SCG_OuterLog
import SCG_PartialOracle
import SCG_RawRecovery
import SCG_Recorder
import SCG_SecondCode
import SCG_SecondTraceLog
import SCG_Selection
import SCG_SharedNative
import SCG_SourceAcceptance
import SCG_WorldQuantifiers
import SCG_WrapperLog
set_option autoImplicit false

#print axioms AspisR1.Rc7_Top.deployed
#print axioms AspisR1.SCG_AcceptedExecution.first_reply
#print axioms AspisR1.SCG_AcceptedPair.replies
#print axioms AspisR1.SCG_AcceptedShape.replies
#print axioms AspisR1.SCG_BatchBody.dictionary
#print axioms AspisR1.SCG_BatchCode.current
#print axioms AspisR1.SCG_BatchCode.stage
#print axioms AspisR1.SCG_BatchDictionary.loop
#print axioms AspisR1.SCG_BatchDictionary.tree
#print axioms AspisR1.SCG_BatchDictionary.values
#print axioms AspisR1.SCG_BatchDictionary.code
#print axioms AspisR1.SCG_Charge.charged
#print axioms AspisR1.SCG_CodeMap.log
#print axioms AspisR1.SCG_CodeMap.ideal_log
#print axioms AspisR1.SCG_CodeMap.lift_log
#print axioms AspisR1.SCG_Composition.native_join_or_source_collision
#print axioms AspisR1.SCG_FirstCode.code
#print axioms AspisR1.SCG_FirstTraceLog.first
#print axioms AspisR1.SCG_NativeAccount.accepted
#print axioms AspisR1.SCG_Nonvacuity.joint
#print axioms AspisR1.SCG_OuterLog.flatten
#print axioms AspisR1.SCG_PartialOracle.syscall
#print axioms AspisR1.SCG_PartialOracle.realization
#print axioms AspisR1.SCG_PartialOracle.not_reverse
#print axioms AspisR1.SCG_RawRecovery.same
#print axioms AspisR1.SCG_RawRecovery.trans
#print axioms AspisR1.SCG_Recorder.select_congr
#print axioms AspisR1.SCG_SecondCode.common
#print axioms AspisR1.SCG_SecondCode.code
#print axioms AspisR1.SCG_SecondTraceLog.second
#print axioms AspisR1.SCG_Selection.actual
#print axioms AspisR1.SCG_SharedNative.accepted
#print axioms AspisR1.SCG_SourceAcceptance.installed
#print axioms AspisR1.SCG_WorldQuantifiers.worlds
#print axioms AspisR1.SCG_WorldQuantifiers.observations
#print axioms AspisR1.SCG_WrapperLog.lifted
#print axioms AspisR1.SCG_WrapperLog.purely
#print axioms AspisR1.SCG_WrapperLog.first
#print axioms AspisR1.SCG_WrapperLog.second
