import Hir_AcceptedDriver
import Hir_AcceptedInputs
import Hir_Authenticated
import Hir_BirthCuts
import Hir_BirthReads
import Hir_BirthSuffix
import Hir_Call
import Hir_CallBirth
import Hir_CallClassify
import Hir_CallLog
import Hir_CallSource
import Hir_CallSuccess
import Hir_CallTotal
import Hir_Choice
import Hir_ChoiceLog
import Hir_CommonEvent
import Hir_CutBindingTransport
import Hir_ExactMargin
import Hir_Factory
import Hir_FactoryCharge
import Hir_FactoryLoad
import Hir_FirstChoice
import Hir_ForeignBack
import Hir_GenesisOrigin
import Hir_IdealJoint
import Hir_IdealLifetime
import Hir_InstalledReader
import Hir_LifetimeBinding
import Hir_LifetimeBudget
import Hir_LifetimeExperiment
import Hir_LifetimeJoint
import Hir_LifetimeLog
import Hir_LifetimeNative
import Hir_LifetimeVersion
import Hir_NoFault
import Hir_NoFaultTransport
import Hir_NoUnwrittenAcceptance
import Hir_ObservedFailure
import Hir_PartialOracle
import Hir_PartialPrefix
import Hir_ProvenanceModel
import Hir_ReaderEntry
import Hir_ReaderMarker
import Hir_RecordErasure
import Hir_RecordNative
import Hir_Recorded
import Hir_RuntimeNonvacuity
import Hir_RuntimeQueryNonvacuity
import Hir_Schedule
import Hir_ScheduleLog
import Hir_ScheduleOrigin
import Hir_ScheduleSource
import Hir_ScheduleTrace
import Hir_Search
import Hir_SelectAssociation
import Hir_SelectOne
import Hir_SelectedBinding
import Hir_SelectedBudget
import Hir_SelectedClean
import Hir_SelectedCommonEvent
import Hir_SelectedDriver
import Hir_SelectedExecution
import Hir_SelectedInputs
import Hir_SelectedJoint
import Hir_SelectedOrigin
import Hir_SelectedVersion
import Hir_SyscallStatusGap
import Hir_TotalRecorded
import Hir_WriterCharge
import Hir_WriterSelect
import Hir_Zero
import T2R_Top
set_option autoImplicit false
#print axioms AspisR1.Hir_AcceptedDriver.accepted
#print axioms AspisR1.Hir_AcceptedInputs.accepted
#print axioms AspisR1.Hir_Authenticated.on_cuts
#print axioms AspisR1.Hir_BirthCuts.source
#print axioms AspisR1.Hir_BirthReads.source_reads
#print axioms AspisR1.Hir_BirthSuffix.suffix
#print axioms AspisR1.Hir_CallBirth.unchanged_or_birth
#print axioms AspisR1.Hir_CallClassify.classified
#print axioms AspisR1.Hir_CallLog.exact_log
#print axioms AspisR1.Hir_CallSource.first_result
#print axioms AspisR1.Hir_CallSource.second_result
#print axioms AspisR1.Hir_CallSource.effect
#print axioms AspisR1.Hir_CallSuccess.effect
#print axioms AspisR1.Hir_CallTotal.exact
#print axioms AspisR1.Hir_Choice.selected
#print axioms AspisR1.Hir_Choice.charged
#print axioms AspisR1.Hir_ChoiceLog.exact
#print axioms AspisR1.Hir_ChoiceLog.budget
#print axioms AspisR1.Hir_CommonEvent.subset
#print axioms AspisR1.Hir_CutBindingTransport.same_pair
#print axioms AspisR1.Hir_ExactMargin.event_margin
#print axioms AspisR1.Hir_FactoryCharge.reads
#print axioms AspisR1.Hir_FactoryLoad.selected
#print axioms AspisR1.Hir_FactoryLoad.entry
#print axioms AspisR1.Hir_FirstChoice.selected
#print axioms AspisR1.Hir_FirstChoice.charged
#print axioms AspisR1.Hir_ForeignBack.unchanged
#print axioms AspisR1.Hir_GenesisOrigin.selected_writer
#print axioms AspisR1.Hir_IdealJoint.exact
#print axioms AspisR1.Hir_IdealJoint.one_loss
#print axioms AspisR1.Hir_IdealLifetime.program_eq
#print axioms AspisR1.Hir_IdealLifetime.total_instance
#print axioms AspisR1.Hir_InstalledReader.marker
#print axioms AspisR1.Hir_LifetimeBinding.binding_or_collision
#print axioms AspisR1.Hir_LifetimeBudget.second
#print axioms AspisR1.Hir_LifetimeBudget.source
#print axioms AspisR1.Hir_LifetimeJoint.source_budget
#print axioms AspisR1.Hir_LifetimeJoint.one_loss
#print axioms AspisR1.Hir_LifetimeLog.exact_reads
#print axioms AspisR1.Hir_LifetimeNative.result
#print axioms AspisR1.Hir_LifetimeVersion.causal_pair
#print axioms AspisR1.Hir_NoFault.of_total
#print axioms AspisR1.Hir_NoFaultTransport.program_eq
#print axioms AspisR1.Hir_NoFaultTransport.every_outcome
#print axioms AspisR1.Hir_NoUnwrittenAcceptance.rejects
#print axioms AspisR1.Hir_ObservedFailure.one_loss
#print axioms AspisR1.Hir_PartialOracle.exact
#print axioms AspisR1.Hir_PartialPrefix.read_prefix
#print axioms AspisR1.Hir_PartialPrefix.budget
#print axioms AspisR1.Hir_ReaderEntry.marker
#print axioms AspisR1.Hir_ReaderEntry.owner
#print axioms AspisR1.Hir_ReaderMarker.resume
#print axioms AspisR1.Hir_RecordErasure.exact
#print axioms AspisR1.Hir_RecordNative.observed
#print axioms AspisR1.Hir_RecordNative.result
#print axioms AspisR1.Hir_RuntimeNonvacuity.genesis
#print axioms AspisR1.Hir_RuntimeNonvacuity.zero
#print axioms AspisR1.Hir_RuntimeNonvacuity.reached
#print axioms AspisR1.Hir_RuntimeNonvacuity.admissibility
#print axioms AspisR1.Hir_RuntimeQueryNonvacuity.source
#print axioms AspisR1.Hir_ScheduleLog.exact_reads
#print axioms AspisR1.Hir_ScheduleOrigin.origin_or_initial
#print axioms AspisR1.Hir_ScheduleSource.result
#print axioms AspisR1.Hir_ScheduleTrace.classified
#print axioms AspisR1.Hir_ScheduleTrace.protection
#print axioms AspisR1.Hir_Search.sound
#print axioms AspisR1.Hir_Search.complete
#print axioms AspisR1.Hir_SelectAssociation.source
#print axioms AspisR1.Hir_SelectOne.sound
#print axioms AspisR1.Hir_SelectOne.complete
#print axioms AspisR1.Hir_SelectedBinding.binding_or_collision
#print axioms AspisR1.Hir_SelectedBudget.source
#print axioms AspisR1.Hir_SelectedClean.exists_clean
#print axioms AspisR1.Hir_SelectedCommonEvent.subset
#print axioms AspisR1.Hir_SelectedDriver.accepted
#print axioms AspisR1.Hir_SelectedExecution.selected
#print axioms AspisR1.Hir_SelectedInputs.accepted
#print axioms AspisR1.Hir_SelectedJoint.source_budget
#print axioms AspisR1.Hir_SelectedJoint.one_loss
#print axioms AspisR1.Hir_SelectedOrigin.causal_writer
#print axioms AspisR1.Hir_SelectedVersion.on_cuts
#print axioms AspisR1.Hir_SyscallStatusGap.status_gap
#print axioms AspisR1.Hir_TotalRecorded.program_eq
#print axioms AspisR1.Hir_WriterCharge.reached_reads
#print axioms AspisR1.Hir_WriterCharge.charged
#print axioms AspisR1.Hir_Zero.not_initialized
#print axioms AspisR1.T2R_Top.deployed
