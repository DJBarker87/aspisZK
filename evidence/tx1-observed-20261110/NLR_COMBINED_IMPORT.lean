import NLO_COMBINED_IMPORT
import NLJ_COMBINED_IMPORT
import NLC_COMBINED_IMPORT
import NLR_ClaimsReservation
import NLR_ConvertedReply
import NLR_FinishModelDomain
import NLR_FinishReservation
import NLR_ObservedFinish
import NLR_ObservedSuccess
import NLR_ObserverSites
import NLR_PrepareAll
import NLR_PrepareArgumentDomains
import NLR_PrepareComplete
import NLR_PrepareDenote
import NLR_PrepareExact
import NLR_PrepareFinalSource
import NLR_PrepareFold
import NLR_PrepareFrame_allocate
import NLR_PrepareFrame_constructor
import NLR_PrepareFrame_expandSemantic
import NLR_PrepareFrame_expandValues
import NLR_PrepareFrame_mapSemantic
import NLR_PrepareFrame_mark
import NLR_PrepareFrame_rebuild
import NLR_PrepareFrame_semantic
import NLR_PrepareFrame_semanticRange
import NLR_PrepareFrame_split
import NLR_PrepareFrame_valueRange
import NLR_PrepareFrame_view
import NLR_PrepareInitialized
import NLR_PreparePrefixBound
import NLR_PrepareProgress_allocate
import NLR_PrepareProgress_constructor
import NLR_PrepareProgress_expandSemantic
import NLR_PrepareProgress_expandValues
import NLR_PrepareProgress_mapSemantic
import NLR_PrepareProgress_mark
import NLR_PrepareProgress_rebuild
import NLR_PrepareProgress_semantic
import NLR_PrepareProgress_semanticRange
import NLR_PrepareProgress_split
import NLR_PrepareProgress_valueRange
import NLR_PrepareProgress_view
import NLR_PrepareReachedDomain
import NLR_PrepareRun_allocate
import NLR_PrepareRun_constructor
import NLR_PrepareRun_expandSemantic
import NLR_PrepareRun_expandValues
import NLR_PrepareRun_mapSemantic
import NLR_PrepareRun_mark
import NLR_PrepareRun_rebuild
import NLR_PrepareRun_semantic
import NLR_PrepareRun_semanticRange
import NLR_PrepareRun_split
import NLR_PrepareRun_valueRange
import NLR_PrepareRun_view
import NLR_PrepareSemantic137
import NLR_PrepareSplitExtent
import NLR_PrepareStep137
import NLR_PrepareTailSource
import NLR_PrepareTails
import NLR_PreparedSemanticClause
import NLR_RowSpec087
import NLR_RowSpec137
import NLR_SemanticCallerResult
import NLR_SemanticFinishCaller
import NLR_Statements
import NLR_WindowFrame

set_option pp.proofs false
#print axioms AspisR1.RPx_Deployed.deployed
#check @AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NLR_ClaimsReservation.success
#check @AspisR1.NLR_ClaimsReservation.success
#print axioms AspisR1.NLR_ConvertedReply.success
#check @AspisR1.NLR_ConvertedReply.success
#print axioms AspisR1.NLR_FinishModelDomain.reached
#check @AspisR1.NLR_FinishModelDomain.reached
#print axioms AspisR1.NLR_FinishReservation.constructor_clause
#check @AspisR1.NLR_FinishReservation.constructor_clause
#print axioms AspisR1.NLR_FinishReservation.source
#check @AspisR1.NLR_FinishReservation.source
#print axioms AspisR1.NLR_ObservedFinish.reached
#check @AspisR1.NLR_ObservedFinish.reached
#print axioms AspisR1.NLR_ObservedSuccess.bind_return
#check @AspisR1.NLR_ObservedSuccess.bind_return
#print axioms AspisR1.NLR_ObservedSuccess.lift_run
#check @AspisR1.NLR_ObservedSuccess.lift_run
#print axioms AspisR1.NLR_ObserverSites.mark0
#check @AspisR1.NLR_ObserverSites.mark0
#print axioms AspisR1.NLR_ObserverSites.mark1
#check @AspisR1.NLR_ObserverSites.mark1
#print axioms AspisR1.NLR_Prepare.decrease
#check @AspisR1.NLR_Prepare.decrease
#print axioms AspisR1.NLR_Prepare.exact_source
#check @AspisR1.NLR_Prepare.exact_source
#print axioms AspisR1.NLR_Prepare.frame_allocate
#check @AspisR1.NLR_Prepare.frame_allocate
#print axioms AspisR1.NLR_Prepare.frame_constructor
#check @AspisR1.NLR_Prepare.frame_constructor
#print axioms AspisR1.NLR_Prepare.frame_expandSemantic
#check @AspisR1.NLR_Prepare.frame_expandSemantic
#print axioms AspisR1.NLR_Prepare.frame_expandValues
#check @AspisR1.NLR_Prepare.frame_expandValues
#print axioms AspisR1.NLR_Prepare.frame_mapSemantic
#check @AspisR1.NLR_Prepare.frame_mapSemantic
#print axioms AspisR1.NLR_Prepare.frame_mark
#check @AspisR1.NLR_Prepare.frame_mark
#print axioms AspisR1.NLR_Prepare.frame_rebuild
#check @AspisR1.NLR_Prepare.frame_rebuild
#print axioms AspisR1.NLR_Prepare.frame_semantic
#check @AspisR1.NLR_Prepare.frame_semantic
#print axioms AspisR1.NLR_Prepare.frame_semanticRange
#check @AspisR1.NLR_Prepare.frame_semanticRange
#print axioms AspisR1.NLR_Prepare.frame_split
#check @AspisR1.NLR_Prepare.frame_split
#print axioms AspisR1.NLR_Prepare.frame_valueRange
#check @AspisR1.NLR_Prepare.frame_valueRange
#print axioms AspisR1.NLR_Prepare.frame_view
#check @AspisR1.NLR_Prepare.frame_view
#print axioms AspisR1.NLR_Prepare.input_frame
#check @AspisR1.NLR_Prepare.input_frame
#print axioms AspisR1.NLR_Prepare.progress_allocate
#check @AspisR1.NLR_Prepare.progress_allocate
#print axioms AspisR1.NLR_Prepare.progress_constructor
#check @AspisR1.NLR_Prepare.progress_constructor
#print axioms AspisR1.NLR_Prepare.progress_expandSemantic
#check @AspisR1.NLR_Prepare.progress_expandSemantic
#print axioms AspisR1.NLR_Prepare.progress_expandValues
#check @AspisR1.NLR_Prepare.progress_expandValues
#print axioms AspisR1.NLR_Prepare.progress_mapSemantic
#check @AspisR1.NLR_Prepare.progress_mapSemantic
#print axioms AspisR1.NLR_Prepare.progress_mark
#check @AspisR1.NLR_Prepare.progress_mark
#print axioms AspisR1.NLR_Prepare.progress_rebuild
#check @AspisR1.NLR_Prepare.progress_rebuild
#print axioms AspisR1.NLR_Prepare.progress_semantic
#check @AspisR1.NLR_Prepare.progress_semantic
#print axioms AspisR1.NLR_Prepare.progress_semanticRange
#check @AspisR1.NLR_Prepare.progress_semanticRange
#print axioms AspisR1.NLR_Prepare.progress_split
#check @AspisR1.NLR_Prepare.progress_split
#print axioms AspisR1.NLR_Prepare.progress_valueRange
#check @AspisR1.NLR_Prepare.progress_valueRange
#print axioms AspisR1.NLR_Prepare.progress_view
#check @AspisR1.NLR_Prepare.progress_view
#print axioms AspisR1.NLR_Prepare.rank_positive
#check @AspisR1.NLR_Prepare.rank_positive
#print axioms AspisR1.NLR_Prepare.run_allocate
#check @AspisR1.NLR_Prepare.run_allocate
#print axioms AspisR1.NLR_Prepare.run_constructor
#check @AspisR1.NLR_Prepare.run_constructor
#print axioms AspisR1.NLR_Prepare.run_expandSemantic
#check @AspisR1.NLR_Prepare.run_expandSemantic
#print axioms AspisR1.NLR_Prepare.run_expandValues
#check @AspisR1.NLR_Prepare.run_expandValues
#print axioms AspisR1.NLR_Prepare.run_mapSemantic
#check @AspisR1.NLR_Prepare.run_mapSemantic
#print axioms AspisR1.NLR_Prepare.run_mark
#check @AspisR1.NLR_Prepare.run_mark
#print axioms AspisR1.NLR_Prepare.run_rebuild
#check @AspisR1.NLR_Prepare.run_rebuild
#print axioms AspisR1.NLR_Prepare.run_semantic
#check @AspisR1.NLR_Prepare.run_semantic
#print axioms AspisR1.NLR_Prepare.run_semanticRange
#check @AspisR1.NLR_Prepare.run_semanticRange
#print axioms AspisR1.NLR_Prepare.run_split
#check @AspisR1.NLR_Prepare.run_split
#print axioms AspisR1.NLR_Prepare.run_valueRange
#check @AspisR1.NLR_Prepare.run_valueRange
#print axioms AspisR1.NLR_Prepare.run_view
#check @AspisR1.NLR_Prepare.run_view
#print axioms AspisR1.NLR_Prepare.source
#check @AspisR1.NLR_Prepare.source
#print axioms AspisR1.NLR_Prepare.source_fold
#check @AspisR1.NLR_Prepare.source_fold
#print axioms AspisR1.NLR_Prepare.source_frame
#check @AspisR1.NLR_Prepare.source_frame
#print axioms AspisR1.NLR_Prepare.source_progress
#check @AspisR1.NLR_Prepare.source_progress
#print axioms AspisR1.NLR_Prepare.source_run
#check @AspisR1.NLR_Prepare.source_run
#print axioms AspisR1.NLR_PrepareArgumentDomains.source
#check @AspisR1.NLR_PrepareArgumentDomains.source
#print axioms AspisR1.NLR_PrepareComplete.invocation
#check @AspisR1.NLR_PrepareComplete.invocation
#print axioms AspisR1.NLR_PrepareInitialized.source
#check @AspisR1.NLR_PrepareInitialized.source
#print axioms AspisR1.NLR_PreparePrefixBound.length_bound
#check @AspisR1.NLR_PreparePrefixBound.length_bound
#print axioms AspisR1.NLR_PreparePrefixBound.nonempty
#check @AspisR1.NLR_PreparePrefixBound.nonempty
#print axioms AspisR1.NLR_PrepareReachedDomain.semantic_extent
#check @AspisR1.NLR_PrepareReachedDomain.semantic_extent
#print axioms AspisR1.NLR_PrepareReachedDomain.semantic_packet
#check @AspisR1.NLR_PrepareReachedDomain.semantic_packet
#print axioms AspisR1.NLR_PrepareSemantic137.installed
#check @AspisR1.NLR_PrepareSemantic137.installed
#print axioms AspisR1.NLR_PrepareSemantic137.packet
#check @AspisR1.NLR_PrepareSemantic137.packet
#print axioms AspisR1.NLR_PrepareSplitExtent.semantic
#check @AspisR1.NLR_PrepareSplitExtent.semantic
#print axioms AspisR1.NLR_PrepareSplitExtent.split_lengths
#check @AspisR1.NLR_PrepareSplitExtent.split_lengths
#print axioms AspisR1.NLR_PrepareStep137.semantic_step
#check @AspisR1.NLR_PrepareStep137.semantic_step
#print axioms AspisR1.NLR_PrepareTails.tail_source
#check @AspisR1.NLR_PrepareTails.tail_source
#print axioms AspisR1.NLR_PreparedSemanticClause.source
#check @AspisR1.NLR_PreparedSemanticClause.source
#print axioms AspisR1.NLR_SemanticCallerResult.source
#check @AspisR1.NLR_SemanticCallerResult.source
#print axioms AspisR1.NLR_SemanticFinishCaller.reached
#check @AspisR1.NLR_SemanticFinishCaller.reached
#print axioms AspisR1.NLR_WindowFrame.partition
#check @AspisR1.NLR_WindowFrame.partition
#print axioms AspisR1.NLR_WindowFrame.prefix_fields
#check @AspisR1.NLR_WindowFrame.prefix_fields
#print axioms AspisR1.NLR_WindowFrame.three_windows
#check @AspisR1.NLR_WindowFrame.three_windows
#print AspisR1.NLJ_Control137.observed_fold
#print AspisR1.NLR_Prepare.source
#print AspisR1.NLR_Prepare.source_fold
#print AspisR1.NLR_Interface.RowSpec_137
#print AspisR1.NLR_Interface.RowSpec_087
