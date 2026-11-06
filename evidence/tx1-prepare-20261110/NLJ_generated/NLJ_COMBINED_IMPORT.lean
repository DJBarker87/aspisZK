import NLG_COMBINED_IMPORT
import NKQ_COMBINED_IMPORT
import NLC_COMBINED_IMPORT
import NLJ_ByteWindows
import NLJ_Child136
import NLJ_CodeRight
import NLJ_Continuation
import NLJ_Control137
import NLJ_ControlBegin
import NLJ_ControlFold
import NLJ_ControlInvocation
import NLJ_ControlParse
import NLJ_ControlPublic
import NLJ_ControlStep
import NLJ_FinishPacket
import NLJ_Frame_begin
import NLJ_Frame_finish
import NLJ_Frame_mark0
import NLJ_Frame_mark1
import NLJ_Frame_parse
import NLJ_Frame_publicTranscript
import NLJ_InstalledBoundaries
import NLJ_Monad
import NLJ_ObservedAll
import NLJ_ObservedDenote
import NLJ_ObservedDirect
import NLJ_ObservedExact
import NLJ_ObservedFold
import NLJ_ObservedInitial
import NLJ_ObservedInvariants
import NLJ_ObservedState
import NLJ_ObservedStep
import NLJ_ObservedWindows
import NLJ_Occurrence_begin
import NLJ_Occurrence_finish
import NLJ_Occurrence_mark0
import NLJ_Occurrence_mark1
import NLJ_Occurrence_parse
import NLJ_Occurrence_publicTranscript
import NLJ_PrepareFold
import NLJ_PrepareGoal
import NLJ_PrepareMap
import NLJ_PrepareState
import NLJ_PrepareStep
import NLJ_PrepareWindow_allocate
import NLJ_PrepareWindow_constructor
import NLJ_PrepareWindow_expandSemantic
import NLJ_PrepareWindow_expandValues
import NLJ_PrepareWindow_mapSemantic
import NLJ_PrepareWindow_mark
import NLJ_PrepareWindow_rebuild
import NLJ_PrepareWindow_semantic
import NLJ_PrepareWindow_semanticRange
import NLJ_PrepareWindow_split
import NLJ_PrepareWindow_valueRange
import NLJ_PrepareWindow_view
import NLJ_Progress_begin
import NLJ_Progress_finish
import NLJ_Progress_mark0
import NLJ_Progress_mark1
import NLJ_Progress_parse
import NLJ_Progress_publicTranscript
import NLJ_RoundPort
import NLJ_RowSpec081
import NLJ_RowSpec094
import NLJ_RunAlgebra
import NLJ_Run_begin
import NLJ_Run_finish
import NLJ_Run_mark0
import NLJ_Run_mark1
import NLJ_Run_parse
import NLJ_Run_publicTranscript
import NLJ_ScanCaller
import NLJ_Tx1Fold
import NLJ_Tx1State
import NLJ_Tx1Step
import NLJ_ViewCaller

-- No CLOSED row roots: conditional source folds only; physical native association remains OPEN.
#print axioms AspisR1.RPx_Deployed.deployed
#check @AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NLJ_ByteWindows.copy_window
#check @AspisR1.NLJ_ByteWindows.copy_window
#print axioms AspisR1.NLJ_ByteWindows.list_windows
#check @AspisR1.NLJ_ByteWindows.list_windows
#print axioms AspisR1.NLJ_CodeRight.right
#check @AspisR1.NLJ_CodeRight.right
#print axioms AspisR1.NLJ_CodeRight.same
#check @AspisR1.NLJ_CodeRight.same
#print axioms AspisR1.NLJ_Control137.begin_step
#check @AspisR1.NLJ_Control137.begin_step
#print axioms AspisR1.NLJ_Control137.observed_fold
#check @AspisR1.NLJ_Control137.observed_fold
#print axioms AspisR1.NLJ_Control137.parser
#check @AspisR1.NLJ_Control137.parser
#print axioms AspisR1.NLJ_Control137.public_step
#check @AspisR1.NLJ_Control137.public_step
#print axioms AspisR1.NLJ_Control137.source_cuts
#check @AspisR1.NLJ_Control137.source_cuts
#print axioms AspisR1.NLJ_Control137.source_step
#check @AspisR1.NLJ_Control137.source_step
#print axioms AspisR1.NLJ_InstalledBoundaries.finish
#check @AspisR1.NLJ_InstalledBoundaries.finish
#print axioms AspisR1.NLJ_Monad.bind_assoc
#check @AspisR1.NLJ_Monad.bind_assoc
#print axioms AspisR1.NLJ_Monad.bind_pure
#check @AspisR1.NLJ_Monad.bind_pure
#print axioms AspisR1.NLJ_Observed.decrease
#check @AspisR1.NLJ_Observed.decrease
#print axioms AspisR1.NLJ_Observed.events_from_cuts
#check @AspisR1.NLJ_Observed.events_from_cuts
#print axioms AspisR1.NLJ_Observed.exact_source
#check @AspisR1.NLJ_Observed.exact_source
#print axioms AspisR1.NLJ_Observed.finish_packet
#check @AspisR1.NLJ_Observed.finish_packet
#print axioms AspisR1.NLJ_Observed.fold_from_steps
#check @AspisR1.NLJ_Observed.fold_from_steps
#print axioms AspisR1.NLJ_Observed.frame_begin
#check @AspisR1.NLJ_Observed.frame_begin
#print axioms AspisR1.NLJ_Observed.frame_finish
#check @AspisR1.NLJ_Observed.frame_finish
#print axioms AspisR1.NLJ_Observed.frame_mark0
#check @AspisR1.NLJ_Observed.frame_mark0
#print axioms AspisR1.NLJ_Observed.frame_mark1
#check @AspisR1.NLJ_Observed.frame_mark1
#print axioms AspisR1.NLJ_Observed.frame_parse
#check @AspisR1.NLJ_Observed.frame_parse
#print axioms AspisR1.NLJ_Observed.frame_publicTranscript
#check @AspisR1.NLJ_Observed.frame_publicTranscript
#print axioms AspisR1.NLJ_Observed.initial_fold
#check @AspisR1.NLJ_Observed.initial_fold
#print axioms AspisR1.NLJ_Observed.initial_source
#check @AspisR1.NLJ_Observed.initial_source
#print axioms AspisR1.NLJ_Observed.input_frame
#check @AspisR1.NLJ_Observed.input_frame
#print axioms AspisR1.NLJ_Observed.occurrence_begin
#check @AspisR1.NLJ_Observed.occurrence_begin
#print axioms AspisR1.NLJ_Observed.occurrence_finish
#check @AspisR1.NLJ_Observed.occurrence_finish
#print axioms AspisR1.NLJ_Observed.occurrence_mark0
#check @AspisR1.NLJ_Observed.occurrence_mark0
#print axioms AspisR1.NLJ_Observed.occurrence_mark1
#check @AspisR1.NLJ_Observed.occurrence_mark1
#print axioms AspisR1.NLJ_Observed.occurrence_parse
#check @AspisR1.NLJ_Observed.occurrence_parse
#print axioms AspisR1.NLJ_Observed.occurrence_publicTranscript
#check @AspisR1.NLJ_Observed.occurrence_publicTranscript
#print axioms AspisR1.NLJ_Observed.progress_begin
#check @AspisR1.NLJ_Observed.progress_begin
#print axioms AspisR1.NLJ_Observed.progress_finish
#check @AspisR1.NLJ_Observed.progress_finish
#print axioms AspisR1.NLJ_Observed.progress_mark0
#check @AspisR1.NLJ_Observed.progress_mark0
#print axioms AspisR1.NLJ_Observed.progress_mark1
#check @AspisR1.NLJ_Observed.progress_mark1
#print axioms AspisR1.NLJ_Observed.progress_parse
#check @AspisR1.NLJ_Observed.progress_parse
#print axioms AspisR1.NLJ_Observed.progress_publicTranscript
#check @AspisR1.NLJ_Observed.progress_publicTranscript
#print axioms AspisR1.NLJ_Observed.rank_positive
#check @AspisR1.NLJ_Observed.rank_positive
#print axioms AspisR1.NLJ_Observed.run_begin
#check @AspisR1.NLJ_Observed.run_begin
#print axioms AspisR1.NLJ_Observed.run_finish
#check @AspisR1.NLJ_Observed.run_finish
#print axioms AspisR1.NLJ_Observed.run_mark0
#check @AspisR1.NLJ_Observed.run_mark0
#print axioms AspisR1.NLJ_Observed.run_mark1
#check @AspisR1.NLJ_Observed.run_mark1
#print axioms AspisR1.NLJ_Observed.run_parse
#check @AspisR1.NLJ_Observed.run_parse
#print axioms AspisR1.NLJ_Observed.run_publicTranscript
#check @AspisR1.NLJ_Observed.run_publicTranscript
#print axioms AspisR1.NLJ_Observed.run_step
#check @AspisR1.NLJ_Observed.run_step
#print axioms AspisR1.NLJ_Observed.source_frame
#check @AspisR1.NLJ_Observed.source_frame
#print axioms AspisR1.NLJ_Observed.source_invocation
#check @AspisR1.NLJ_Observed.source_invocation
#print axioms AspisR1.NLJ_Observed.source_progress
#check @AspisR1.NLJ_Observed.source_progress
#print axioms AspisR1.NLJ_ObservedDirect.source
#check @AspisR1.NLJ_ObservedDirect.source
#print axioms AspisR1.NLJ_Prepare.carry
#check @AspisR1.NLJ_Prepare.carry
#print axioms AspisR1.NLJ_Prepare.error
#check @AspisR1.NLJ_Prepare.error
#print axioms AspisR1.NLJ_Prepare.fold_from_steps
#check @AspisR1.NLJ_Prepare.fold_from_steps
#print axioms AspisR1.NLJ_Prepare.step_allocate
#check @AspisR1.NLJ_Prepare.step_allocate
#print axioms AspisR1.NLJ_Prepare.step_constructor
#check @AspisR1.NLJ_Prepare.step_constructor
#print axioms AspisR1.NLJ_Prepare.step_expandSemantic
#check @AspisR1.NLJ_Prepare.step_expandSemantic
#print axioms AspisR1.NLJ_Prepare.step_expandValues
#check @AspisR1.NLJ_Prepare.step_expandValues
#print axioms AspisR1.NLJ_Prepare.step_mapSemantic
#check @AspisR1.NLJ_Prepare.step_mapSemantic
#print axioms AspisR1.NLJ_Prepare.step_mark
#check @AspisR1.NLJ_Prepare.step_mark
#print axioms AspisR1.NLJ_Prepare.step_rebuild
#check @AspisR1.NLJ_Prepare.step_rebuild
#print axioms AspisR1.NLJ_Prepare.step_semantic
#check @AspisR1.NLJ_Prepare.step_semantic
#print axioms AspisR1.NLJ_Prepare.step_semanticRange
#check @AspisR1.NLJ_Prepare.step_semanticRange
#print axioms AspisR1.NLJ_Prepare.step_split
#check @AspisR1.NLJ_Prepare.step_split
#print axioms AspisR1.NLJ_Prepare.step_valueRange
#check @AspisR1.NLJ_Prepare.step_valueRange
#print axioms AspisR1.NLJ_Prepare.step_view
#check @AspisR1.NLJ_Prepare.step_view
#print axioms AspisR1.NLJ_RoundPort.rounds
#check @AspisR1.NLJ_RoundPort.rounds
#print axioms AspisR1.NLJ_RunAlgebra.bind_congr
#check @AspisR1.NLJ_RunAlgebra.bind_congr
#print axioms AspisR1.NLJ_RunAlgebra.inl_return
#check @AspisR1.NLJ_RunAlgebra.inl_return
#print axioms AspisR1.NLJ_ScanCaller.domain
#check @AspisR1.NLJ_ScanCaller.domain
#print axioms AspisR1.NLJ_ScanCaller.installed
#check @AspisR1.NLJ_ScanCaller.installed
#print axioms AspisR1.NLJ_ScanCaller.same_original
#check @AspisR1.NLJ_ScanCaller.same_original
#print axioms AspisR1.NLJ_Tx1.source_fold
#check @AspisR1.NLJ_Tx1.source_fold
#print axioms AspisR1.NLJ_ViewCaller.fields
#check @AspisR1.NLJ_ViewCaller.fields
#print axioms AspisR1.NLJ_ViewCaller.semantic_domain
#check @AspisR1.NLJ_ViewCaller.semantic_domain

set_option pp.proofs false
#print AspisR1.NLJ_Observed.initial_source
#print AspisR1.NLJ_Observed.events_from_cuts
#print AspisR1.NLJ_Control137.observed_fold
#print AspisR1.NLJ_Prepare.fold_from_steps
#print AspisR1.NLJ_Tx1.source_fold
