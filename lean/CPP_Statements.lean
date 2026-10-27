import CPP_Acceptance
import CPP_Atomic
import CPP_AtomicAuthenticated
import CPP_AtomicBatchSuffix
import CPP_AtomicBinding
import CPP_AtomicBirthSuffix
import CPP_AtomicBudget
import CPP_AtomicClose
import CPP_AtomicInputs
import CPP_AtomicJoint
import CPP_AtomicLaws
import CPP_AtomicLifetime
import CPP_AtomicNonvacuity
import CPP_AtomicOrigin
import CPP_AtomicRecord
import CPP_AtomicRecordErasure
import CPP_AtomicRecordNative
import CPP_AtomicRecorded
import CPP_AtomicRunOrigin
import CPP_AtomicRunSource
import CPP_AtomicRunTrace
import CPP_AtomicSchedule
import CPP_AtomicSelected
import CPP_AtomicSites
import CPP_AtomicSource
import CPP_AtomicTop
import CPP_AtomicTrace
import CPP_AtomicVersion
import CPP_BankCache
import CPP_BankCacheFrames
import CPP_BankEvents
import CPP_BankFrame
import CPP_BankHistory
import CPP_BankNonvacuity
import CPP_BankSourceLoad
import CPP_BankState
import CPP_CallerSource
import CPP_Classify
import CPP_Close
import CPP_Compatibility
import CPP_Dispatch
import CPP_FullResult
import CPP_Gates
import CPP_GuardSource
import CPP_Install
import CPP_InstalledTop
import CPP_Invocation
import CPP_LogNonvacuity
import CPP_Metadata
import CPP_Nonvacuity
import CPP_Oracle
import CPP_OracleSource
import CPP_Origin
import CPP_ProgramErasure
import CPP_ProtectedClose
import CPP_ProtectedResult
import CPP_ProtectedTop
import CPP_Protection
import CPP_RunErasure
import CPP_RuntimeTop
import CPP_Schedule
import CPP_Second
import CPP_Selected
import CPP_Top
import CPP_TraceAppend
import CPP_Write
import CPP_Endpoint
import CPP_ProtectedObservation
import CPP_ResultOrder
import CPP_BankBinding
import CPP_AtomicDriver
import CPP_AtomicClean
import CPP_BankCacheGap
import CPP_CommitGeometry
set_option pp.proofs false

/- Display-only audit. The historical root remains unchanged. Compare the
actual quantified statements and both old/new continuation definitions. -/
#check AspisR1.T2R_Top.deployed
#check AspisR1.CPP_Endpoint.deployed
#check AspisR1.CPP_ResultOrder.original
#check AspisR1.CPP_ProtectedObservation.checkpoint
#print AspisR1.T2R_Acceptance.Facts
#print AspisR1.CPP_Acceptance.Facts
#print AspisR1.T2R_CallerSource.Outcome
#print AspisR1.CPP_CallerSource.Outcome
#print AspisR1.CPP_ProtectedResult.Outcome
#check AspisR1.CPP_AtomicJoint.one_loss
#check AspisR1.CPP_BankBinding.binding
#check AspisR1.CPP_BankCacheGap.marker_not_sufficient

/- Final accepted-axioms audit of every new top theorem/constructor. -/
#print axioms AspisR1.CPP_AtomicAuthenticated.on_cuts
#print axioms AspisR1.CPP_AtomicBatchSuffix.suffix
#print axioms AspisR1.CPP_AtomicBinding.binding_or_collision
#print axioms AspisR1.CPP_AtomicBirthSuffix.suffix
#print axioms AspisR1.CPP_AtomicBudget.source
#print axioms AspisR1.CPP_AtomicClean.exists_clean
#print axioms AspisR1.CPP_AtomicClose.closed
#print axioms AspisR1.CPP_AtomicDriver.accepted
#print axioms AspisR1.CPP_AtomicInputs.accepted
#print axioms AspisR1.CPP_AtomicJoint.one_loss
#print axioms AspisR1.CPP_AtomicJoint.source_budget
#print axioms AspisR1.CPP_AtomicLaws.commit
#print axioms AspisR1.CPP_AtomicLaws.reply
#print axioms AspisR1.CPP_AtomicLaws.rollback
#print axioms AspisR1.CPP_AtomicLifetime.result
#print axioms AspisR1.CPP_AtomicNonvacuity.queried
#print axioms AspisR1.CPP_AtomicNonvacuity.rollback
#print axioms AspisR1.CPP_AtomicNonvacuity.tentative
#print axioms AspisR1.CPP_AtomicOrigin.origin_or_initial
#print axioms AspisR1.CPP_AtomicRecord.erasure
#print axioms AspisR1.CPP_AtomicRecord.native
#print axioms AspisR1.CPP_AtomicRecordErasure.exact
#print axioms AspisR1.CPP_AtomicRecordNative.result
#print axioms AspisR1.CPP_AtomicRunOrigin.origin_or_initial
#print axioms AspisR1.CPP_AtomicRunSource.result
#print axioms AspisR1.CPP_AtomicRunTrace.classified
#print axioms AspisR1.CPP_AtomicSelected.selected
#print axioms AspisR1.CPP_AtomicSites.member
#print axioms AspisR1.CPP_AtomicSource.evaluation
#print axioms AspisR1.CPP_AtomicSource.native
#print axioms AspisR1.CPP_AtomicTop.deployed
#print axioms AspisR1.CPP_AtomicTrace.classified
#print axioms AspisR1.CPP_AtomicVersion.on_cuts
#print axioms AspisR1.CPP_BankBinding.binding
#print axioms AspisR1.CPP_BankBinding.history_effect
#print axioms AspisR1.CPP_BankCache.dead_image
#print axioms AspisR1.CPP_BankCache.live
#print axioms AspisR1.CPP_BankCache.loaded
#print axioms AspisR1.CPP_BankCache.marker_live
#print axioms AspisR1.CPP_BankCacheFrames.record
#print axioms AspisR1.CPP_BankCacheFrames.remains_cached
#print axioms AspisR1.CPP_BankCacheGap.marker_but_absent
#print axioms AspisR1.CPP_BankCacheGap.marker_not_sufficient
#print axioms AspisR1.CPP_BankEvents.step_effect
#print axioms AspisR1.CPP_BankFrame.initial_positive
#print axioms AspisR1.CPP_BankFrame.step_frame
#print axioms AspisR1.CPP_BankHistory.protection
#print axioms AspisR1.CPP_BankNonvacuity.at_rest
#print axioms AspisR1.CPP_BankNonvacuity.reached
#print axioms AspisR1.CPP_BankSourceLoad.reader_live
#print axioms AspisR1.CPP_BankSourceLoad.writer_live
#print axioms AspisR1.CPP_BankState.entry_balance
#print axioms AspisR1.CPP_Classify.classified
#print axioms AspisR1.CPP_Classify.first_invalid
#print axioms AspisR1.CPP_Classify.first_valid
#print axioms AspisR1.CPP_Classify.rejected
#print axioms AspisR1.CPP_Classify.second_invalid
#print axioms AspisR1.CPP_Classify.second_valid
#print axioms AspisR1.CPP_Close.closed
#print axioms AspisR1.CPP_CommitGeometry.committed
#print axioms AspisR1.CPP_Compatibility.invalid
#print axioms AspisR1.CPP_Compatibility.valid
#print axioms AspisR1.CPP_Dispatch.source
#print axioms AspisR1.CPP_Endpoint.deployed
#print axioms AspisR1.CPP_Gates.first_accepted
#print axioms AspisR1.CPP_Gates.first_rejected
#print axioms AspisR1.CPP_Gates.second_accepted
#print axioms AspisR1.CPP_Gates.second_rejected
#print axioms AspisR1.CPP_GuardSource.exact
#print axioms AspisR1.CPP_Install.clone
#print axioms AspisR1.CPP_Install.key
#print axioms AspisR1.CPP_InstalledTop.deployed
#print axioms AspisR1.CPP_LogNonvacuity.exact
#print axioms AspisR1.CPP_Metadata.first_frame
#print axioms AspisR1.CPP_Metadata.second_frame
#print axioms AspisR1.CPP_Nonvacuity.incompatible
#print axioms AspisR1.CPP_Nonvacuity.reached
#print axioms AspisR1.CPP_Nonvacuity.route
#print axioms AspisR1.CPP_OracleSource.effect
#print axioms AspisR1.CPP_OracleSource.invalid
#print axioms AspisR1.CPP_OracleSource.valid
#print axioms AspisR1.CPP_Origin.selected
#print axioms AspisR1.CPP_ProgramErasure.exact
#print axioms AspisR1.CPP_ProtectedClose.closed
#print axioms AspisR1.CPP_ProtectedObservation.checkpoint
#print axioms AspisR1.CPP_ProtectedTop.deployed
#print axioms AspisR1.CPP_Protection.protection
#print axioms AspisR1.CPP_ResultOrder.original
#print axioms AspisR1.CPP_RunErasure.exact
#print axioms AspisR1.CPP_RuntimeTop.deployed
#print axioms AspisR1.CPP_Second.exact
#print axioms AspisR1.CPP_Selected.one_loss
#print axioms AspisR1.CPP_Selected.version
#print axioms AspisR1.CPP_Top.deployed
#print axioms AspisR1.CPP_TraceAppend.append
#print axioms AspisR1.CPP_Write.committed
#print axioms AspisR1.T2R_Top.deployed
