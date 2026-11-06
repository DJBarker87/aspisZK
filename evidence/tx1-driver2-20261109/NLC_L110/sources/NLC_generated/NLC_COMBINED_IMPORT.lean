import NKW_COMBINED_IMPORT
import NKQ_COMBINED_IMPORT
import NLC_BridgeGoal
import NLC_ConstructExt
import NLC_CopyFrames
import NLC_FinishConstruct
import NLC_FinishFold
import NLC_FinishState
import NLC_FinishStep
import NLC_FinishTerminalMap
import NLC_FrameAlgebra
import NLC_Frame_addExtra
import NLC_Frame_addMask
import NLC_Frame_alpha
import NLC_Frame_blind
import NLC_Frame_circle0
import NLC_Frame_circle1
import NLC_Frame_circleGuard
import NLC_Frame_claims
import NLC_Frame_decode25
import NLC_Frame_decode26
import NLC_Frame_extra28
import NLC_Frame_highArray
import NLC_Frame_lowArray
import NLC_Frame_mapPublic
import NLC_Frame_mark2
import NLC_Frame_mark3
import NLC_Frame_mark4
import NLC_Frame_mark5
import NLC_Frame_mask
import NLC_Frame_multiply
import NLC_Frame_original
import NLC_Frame_payload2
import NLC_Frame_record25a
import NLC_Frame_record25b
import NLC_Frame_record26a
import NLC_Frame_record26b
import NLC_Frame_rootCopy
import NLC_Frame_rounds
import NLC_Frame_stateBefore
import NLC_Frame_terminal
import NLC_Frame_terminalGuard
import NLC_Frame_verified
import NLC_InitializedInvocation
import NLC_LeafSound
import NLC_MapCut
import NLC_Progress
import NLC_Rank
import NLC_Rank0
import NLC_Rank1
import NLC_Rank2
import NLC_Rank3
import NLC_RankBase
import NLC_ReadsReady
import NLC_Ready
import NLC_Ready0
import NLC_Ready1
import NLC_Ready2
import NLC_Ready3
import NLC_ReadyBase
import NLC_SourceActual
import NLC_SourceInvocation
import NLC_Step_addExtra
import NLC_Step_addMask
import NLC_Step_alpha
import NLC_Step_blind
import NLC_Step_circle0
import NLC_Step_circle1
import NLC_Step_circleGuard
import NLC_Step_claims
import NLC_Step_decode25
import NLC_Step_decode26
import NLC_Step_extra28
import NLC_Step_highArray
import NLC_Step_lowArray
import NLC_Step_mapPublic
import NLC_Step_mark2
import NLC_Step_mark3
import NLC_Step_mark4
import NLC_Step_mark5
import NLC_Step_mask
import NLC_Step_multiply
import NLC_Step_original
import NLC_Step_payload2
import NLC_Step_record25a
import NLC_Step_record25b
import NLC_Step_record26a
import NLC_Step_record26b
import NLC_Step_rootCopy
import NLC_Step_rounds
import NLC_Step_stateBefore
import NLC_Step_terminal
import NLC_Step_terminalGuard
import NLC_Step_verified
import NLC_Suboccurrences

-- No row root or native parent fold; source interpreter and local windows only.
#print axioms AspisR1.RPx_Deployed.deployed
#check @AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NLC_ConstructExt.verified_fields
#check @AspisR1.NLC_ConstructExt.verified_fields
#print axioms AspisR1.NLC_CopyFrames.array_windows
#check @AspisR1.NLC_CopyFrames.array_windows
#print axioms AspisR1.NLC_CopyFrames.copied_window
#check @AspisR1.NLC_CopyFrames.copied_window
#print axioms AspisR1.NLC_CopyFrames.disjoint_windows
#check @AspisR1.NLC_CopyFrames.disjoint_windows
#print axioms AspisR1.NLC_CopyFrames.retained_window
#check @AspisR1.NLC_CopyFrames.retained_window
#print axioms AspisR1.NLC_Finish.all_bind
#check @AspisR1.NLC_Finish.all_bind
#print axioms AspisR1.NLC_Finish.all_erase
#check @AspisR1.NLC_Finish.all_erase
#print axioms AspisR1.NLC_Finish.bounded_source_fold
#check @AspisR1.NLC_Finish.bounded_source_fold
#print axioms AspisR1.NLC_Finish.constructor
#check @AspisR1.NLC_Finish.constructor
#print axioms AspisR1.NLC_Finish.fold_from_steps
#check @AspisR1.NLC_Finish.fold_from_steps
#print axioms AspisR1.NLC_Finish.frame_addExtra
#check @AspisR1.NLC_Finish.frame_addExtra
#print axioms AspisR1.NLC_Finish.frame_addMask
#check @AspisR1.NLC_Finish.frame_addMask
#print axioms AspisR1.NLC_Finish.frame_alpha
#check @AspisR1.NLC_Finish.frame_alpha
#print axioms AspisR1.NLC_Finish.frame_blind
#check @AspisR1.NLC_Finish.frame_blind
#print axioms AspisR1.NLC_Finish.frame_circle0
#check @AspisR1.NLC_Finish.frame_circle0
#print axioms AspisR1.NLC_Finish.frame_circle1
#check @AspisR1.NLC_Finish.frame_circle1
#print axioms AspisR1.NLC_Finish.frame_circleGuard
#check @AspisR1.NLC_Finish.frame_circleGuard
#print axioms AspisR1.NLC_Finish.frame_claims
#check @AspisR1.NLC_Finish.frame_claims
#print axioms AspisR1.NLC_Finish.frame_decode25
#check @AspisR1.NLC_Finish.frame_decode25
#print axioms AspisR1.NLC_Finish.frame_decode26
#check @AspisR1.NLC_Finish.frame_decode26
#print axioms AspisR1.NLC_Finish.frame_extra28
#check @AspisR1.NLC_Finish.frame_extra28
#print axioms AspisR1.NLC_Finish.frame_highArray
#check @AspisR1.NLC_Finish.frame_highArray
#print axioms AspisR1.NLC_Finish.frame_lowArray
#check @AspisR1.NLC_Finish.frame_lowArray
#print axioms AspisR1.NLC_Finish.frame_mapPublic
#check @AspisR1.NLC_Finish.frame_mapPublic
#print axioms AspisR1.NLC_Finish.frame_mark2
#check @AspisR1.NLC_Finish.frame_mark2
#print axioms AspisR1.NLC_Finish.frame_mark3
#check @AspisR1.NLC_Finish.frame_mark3
#print axioms AspisR1.NLC_Finish.frame_mark4
#check @AspisR1.NLC_Finish.frame_mark4
#print axioms AspisR1.NLC_Finish.frame_mark5
#check @AspisR1.NLC_Finish.frame_mark5
#print axioms AspisR1.NLC_Finish.frame_mask
#check @AspisR1.NLC_Finish.frame_mask
#print axioms AspisR1.NLC_Finish.frame_multiply
#check @AspisR1.NLC_Finish.frame_multiply
#print axioms AspisR1.NLC_Finish.frame_next
#check @AspisR1.NLC_Finish.frame_next
#print axioms AspisR1.NLC_Finish.frame_original
#check @AspisR1.NLC_Finish.frame_original
#print axioms AspisR1.NLC_Finish.frame_payload2
#check @AspisR1.NLC_Finish.frame_payload2
#print axioms AspisR1.NLC_Finish.frame_put
#check @AspisR1.NLC_Finish.frame_put
#print axioms AspisR1.NLC_Finish.frame_record25a
#check @AspisR1.NLC_Finish.frame_record25a
#print axioms AspisR1.NLC_Finish.frame_record25b
#check @AspisR1.NLC_Finish.frame_record25b
#print axioms AspisR1.NLC_Finish.frame_record26a
#check @AspisR1.NLC_Finish.frame_record26a
#print axioms AspisR1.NLC_Finish.frame_record26b
#check @AspisR1.NLC_Finish.frame_record26b
#print axioms AspisR1.NLC_Finish.frame_rootCopy
#check @AspisR1.NLC_Finish.frame_rootCopy
#print axioms AspisR1.NLC_Finish.frame_rounds
#check @AspisR1.NLC_Finish.frame_rounds
#print axioms AspisR1.NLC_Finish.frame_stateBefore
#check @AspisR1.NLC_Finish.frame_stateBefore
#print axioms AspisR1.NLC_Finish.frame_terminal
#check @AspisR1.NLC_Finish.frame_terminal
#print axioms AspisR1.NLC_Finish.frame_terminalGuard
#check @AspisR1.NLC_Finish.frame_terminalGuard
#print axioms AspisR1.NLC_Finish.frame_verified
#check @AspisR1.NLC_Finish.frame_verified
#print axioms AspisR1.NLC_Finish.fuel_next
#check @AspisR1.NLC_Finish.fuel_next
#print axioms AspisR1.NLC_Finish.fuel_positive
#check @AspisR1.NLC_Finish.fuel_positive
#print axioms AspisR1.NLC_Finish.high_callback
#check @AspisR1.NLC_Finish.high_callback
#print axioms AspisR1.NLC_Finish.initial_fold
#check @AspisR1.NLC_Finish.initial_fold
#print axioms AspisR1.NLC_Finish.initial_ready
#check @AspisR1.NLC_Finish.initial_ready
#print axioms AspisR1.NLC_Finish.initialized
#check @AspisR1.NLC_Finish.initialized
#print axioms AspisR1.NLC_Finish.initialized_read
#check @AspisR1.NLC_Finish.initialized_read
#print axioms AspisR1.NLC_Finish.low_callback
#check @AspisR1.NLC_Finish.low_callback
#print axioms AspisR1.NLC_Finish.map_error
#check @AspisR1.NLC_Finish.map_error
#print axioms AspisR1.NLC_Finish.map_value
#check @AspisR1.NLC_Finish.map_value
#print axioms AspisR1.NLC_Finish.put_frame
#check @AspisR1.NLC_Finish.put_frame
#print axioms AspisR1.NLC_Finish.rank_addExtra
#check @AspisR1.NLC_Finish.rank_addExtra
#print axioms AspisR1.NLC_Finish.rank_addMask
#check @AspisR1.NLC_Finish.rank_addMask
#print axioms AspisR1.NLC_Finish.rank_alpha
#check @AspisR1.NLC_Finish.rank_alpha
#print axioms AspisR1.NLC_Finish.rank_blind
#check @AspisR1.NLC_Finish.rank_blind
#print axioms AspisR1.NLC_Finish.rank_bound
#check @AspisR1.NLC_Finish.rank_bound
#print axioms AspisR1.NLC_Finish.rank_circle0
#check @AspisR1.NLC_Finish.rank_circle0
#print axioms AspisR1.NLC_Finish.rank_circle1
#check @AspisR1.NLC_Finish.rank_circle1
#print axioms AspisR1.NLC_Finish.rank_circleGuard
#check @AspisR1.NLC_Finish.rank_circleGuard
#print axioms AspisR1.NLC_Finish.rank_claims
#check @AspisR1.NLC_Finish.rank_claims
#print axioms AspisR1.NLC_Finish.rank_decode25
#check @AspisR1.NLC_Finish.rank_decode25
#print axioms AspisR1.NLC_Finish.rank_decode26
#check @AspisR1.NLC_Finish.rank_decode26
#print axioms AspisR1.NLC_Finish.rank_extra28
#check @AspisR1.NLC_Finish.rank_extra28
#print axioms AspisR1.NLC_Finish.rank_highArray
#check @AspisR1.NLC_Finish.rank_highArray
#print axioms AspisR1.NLC_Finish.rank_lowArray
#check @AspisR1.NLC_Finish.rank_lowArray
#print axioms AspisR1.NLC_Finish.rank_mapPublic
#check @AspisR1.NLC_Finish.rank_mapPublic
#print axioms AspisR1.NLC_Finish.rank_mark2
#check @AspisR1.NLC_Finish.rank_mark2
#print axioms AspisR1.NLC_Finish.rank_mark3
#check @AspisR1.NLC_Finish.rank_mark3
#print axioms AspisR1.NLC_Finish.rank_mark4
#check @AspisR1.NLC_Finish.rank_mark4
#print axioms AspisR1.NLC_Finish.rank_mark5
#check @AspisR1.NLC_Finish.rank_mark5
#print axioms AspisR1.NLC_Finish.rank_mask
#check @AspisR1.NLC_Finish.rank_mask
#print axioms AspisR1.NLC_Finish.rank_multiply
#check @AspisR1.NLC_Finish.rank_multiply
#print axioms AspisR1.NLC_Finish.rank_next
#check @AspisR1.NLC_Finish.rank_next
#print axioms AspisR1.NLC_Finish.rank_original
#check @AspisR1.NLC_Finish.rank_original
#print axioms AspisR1.NLC_Finish.rank_payload2
#check @AspisR1.NLC_Finish.rank_payload2
#print axioms AspisR1.NLC_Finish.rank_put
#check @AspisR1.NLC_Finish.rank_put
#print axioms AspisR1.NLC_Finish.rank_record25a
#check @AspisR1.NLC_Finish.rank_record25a
#print axioms AspisR1.NLC_Finish.rank_record25b
#check @AspisR1.NLC_Finish.rank_record25b
#print axioms AspisR1.NLC_Finish.rank_record26a
#check @AspisR1.NLC_Finish.rank_record26a
#print axioms AspisR1.NLC_Finish.rank_record26b
#check @AspisR1.NLC_Finish.rank_record26b
#print axioms AspisR1.NLC_Finish.rank_returned
#check @AspisR1.NLC_Finish.rank_returned
#print axioms AspisR1.NLC_Finish.rank_rootCopy
#check @AspisR1.NLC_Finish.rank_rootCopy
#print axioms AspisR1.NLC_Finish.rank_rounds
#check @AspisR1.NLC_Finish.rank_rounds
#print axioms AspisR1.NLC_Finish.rank_stateBefore
#check @AspisR1.NLC_Finish.rank_stateBefore
#print axioms AspisR1.NLC_Finish.rank_terminal
#check @AspisR1.NLC_Finish.rank_terminal
#print axioms AspisR1.NLC_Finish.rank_terminalGuard
#check @AspisR1.NLC_Finish.rank_terminalGuard
#print axioms AspisR1.NLC_Finish.rank_verified
#check @AspisR1.NLC_Finish.rank_verified
#print axioms AspisR1.NLC_Finish.ready_addExtra
#check @AspisR1.NLC_Finish.ready_addExtra
#print axioms AspisR1.NLC_Finish.ready_addMask
#check @AspisR1.NLC_Finish.ready_addMask
#print axioms AspisR1.NLC_Finish.ready_alpha
#check @AspisR1.NLC_Finish.ready_alpha
#print axioms AspisR1.NLC_Finish.ready_blind
#check @AspisR1.NLC_Finish.ready_blind
#print axioms AspisR1.NLC_Finish.ready_circle0
#check @AspisR1.NLC_Finish.ready_circle0
#print axioms AspisR1.NLC_Finish.ready_circle1
#check @AspisR1.NLC_Finish.ready_circle1
#print axioms AspisR1.NLC_Finish.ready_circleGuard
#check @AspisR1.NLC_Finish.ready_circleGuard
#print axioms AspisR1.NLC_Finish.ready_claims
#check @AspisR1.NLC_Finish.ready_claims
#print axioms AspisR1.NLC_Finish.ready_decode25
#check @AspisR1.NLC_Finish.ready_decode25
#print axioms AspisR1.NLC_Finish.ready_decode26
#check @AspisR1.NLC_Finish.ready_decode26
#print axioms AspisR1.NLC_Finish.ready_extra28
#check @AspisR1.NLC_Finish.ready_extra28
#print axioms AspisR1.NLC_Finish.ready_highArray
#check @AspisR1.NLC_Finish.ready_highArray
#print axioms AspisR1.NLC_Finish.ready_lowArray
#check @AspisR1.NLC_Finish.ready_lowArray
#print axioms AspisR1.NLC_Finish.ready_mapPublic
#check @AspisR1.NLC_Finish.ready_mapPublic
#print axioms AspisR1.NLC_Finish.ready_mark2
#check @AspisR1.NLC_Finish.ready_mark2
#print axioms AspisR1.NLC_Finish.ready_mark3
#check @AspisR1.NLC_Finish.ready_mark3
#print axioms AspisR1.NLC_Finish.ready_mark4
#check @AspisR1.NLC_Finish.ready_mark4
#print axioms AspisR1.NLC_Finish.ready_mark5
#check @AspisR1.NLC_Finish.ready_mark5
#print axioms AspisR1.NLC_Finish.ready_mask
#check @AspisR1.NLC_Finish.ready_mask
#print axioms AspisR1.NLC_Finish.ready_multiply
#check @AspisR1.NLC_Finish.ready_multiply
#print axioms AspisR1.NLC_Finish.ready_original
#check @AspisR1.NLC_Finish.ready_original
#print axioms AspisR1.NLC_Finish.ready_payload2
#check @AspisR1.NLC_Finish.ready_payload2
#print axioms AspisR1.NLC_Finish.ready_reads
#check @AspisR1.NLC_Finish.ready_reads
#print axioms AspisR1.NLC_Finish.ready_record25a
#check @AspisR1.NLC_Finish.ready_record25a
#print axioms AspisR1.NLC_Finish.ready_record25b
#check @AspisR1.NLC_Finish.ready_record25b
#print axioms AspisR1.NLC_Finish.ready_record26a
#check @AspisR1.NLC_Finish.ready_record26a
#print axioms AspisR1.NLC_Finish.ready_record26b
#check @AspisR1.NLC_Finish.ready_record26b
#print axioms AspisR1.NLC_Finish.ready_returned
#check @AspisR1.NLC_Finish.ready_returned
#print axioms AspisR1.NLC_Finish.ready_rootCopy
#check @AspisR1.NLC_Finish.ready_rootCopy
#print axioms AspisR1.NLC_Finish.ready_rounds
#check @AspisR1.NLC_Finish.ready_rounds
#print axioms AspisR1.NLC_Finish.ready_stateBefore
#check @AspisR1.NLC_Finish.ready_stateBefore
#print axioms AspisR1.NLC_Finish.ready_terminal
#check @AspisR1.NLC_Finish.ready_terminal
#print axioms AspisR1.NLC_Finish.ready_terminalGuard
#check @AspisR1.NLC_Finish.ready_terminalGuard
#print axioms AspisR1.NLC_Finish.ready_verified
#check @AspisR1.NLC_Finish.ready_verified
#print axioms AspisR1.NLC_Finish.returned_frame
#check @AspisR1.NLC_Finish.returned_frame
#print axioms AspisR1.NLC_Finish.root_occurrences
#check @AspisR1.NLC_Finish.root_occurrences
#print axioms AspisR1.NLC_Finish.setNext_frame
#check @AspisR1.NLC_Finish.setNext_frame
#print axioms AspisR1.NLC_Finish.source_input_frame
#check @AspisR1.NLC_Finish.source_input_frame
#print axioms AspisR1.NLC_Finish.source_invocation
#check @AspisR1.NLC_Finish.source_invocation
#print axioms AspisR1.NLC_Finish.source_major_next
#check @AspisR1.NLC_Finish.source_major_next
#print axioms AspisR1.NLC_Finish.source_progress
#check @AspisR1.NLC_Finish.source_progress
#print axioms AspisR1.NLC_Finish.source_ready_next
#check @AspisR1.NLC_Finish.source_ready_next
#print axioms AspisR1.NLC_Finish.step_addExtra
#check @AspisR1.NLC_Finish.step_addExtra
#print axioms AspisR1.NLC_Finish.step_addMask
#check @AspisR1.NLC_Finish.step_addMask
#print axioms AspisR1.NLC_Finish.step_alpha
#check @AspisR1.NLC_Finish.step_alpha
#print axioms AspisR1.NLC_Finish.step_blind
#check @AspisR1.NLC_Finish.step_blind
#print axioms AspisR1.NLC_Finish.step_circle0
#check @AspisR1.NLC_Finish.step_circle0
#print axioms AspisR1.NLC_Finish.step_circle1
#check @AspisR1.NLC_Finish.step_circle1
#print axioms AspisR1.NLC_Finish.step_circleGuard
#check @AspisR1.NLC_Finish.step_circleGuard
#print axioms AspisR1.NLC_Finish.step_claims
#check @AspisR1.NLC_Finish.step_claims
#print axioms AspisR1.NLC_Finish.step_decode25
#check @AspisR1.NLC_Finish.step_decode25
#print axioms AspisR1.NLC_Finish.step_decode26
#check @AspisR1.NLC_Finish.step_decode26
#print axioms AspisR1.NLC_Finish.step_extra28
#check @AspisR1.NLC_Finish.step_extra28
#print axioms AspisR1.NLC_Finish.step_highArray
#check @AspisR1.NLC_Finish.step_highArray
#print axioms AspisR1.NLC_Finish.step_lowArray
#check @AspisR1.NLC_Finish.step_lowArray
#print axioms AspisR1.NLC_Finish.step_mapPublic
#check @AspisR1.NLC_Finish.step_mapPublic
#print axioms AspisR1.NLC_Finish.step_mark2
#check @AspisR1.NLC_Finish.step_mark2
#print axioms AspisR1.NLC_Finish.step_mark3
#check @AspisR1.NLC_Finish.step_mark3
#print axioms AspisR1.NLC_Finish.step_mark4
#check @AspisR1.NLC_Finish.step_mark4
#print axioms AspisR1.NLC_Finish.step_mark5
#check @AspisR1.NLC_Finish.step_mark5
#print axioms AspisR1.NLC_Finish.step_mask
#check @AspisR1.NLC_Finish.step_mask
#print axioms AspisR1.NLC_Finish.step_multiply
#check @AspisR1.NLC_Finish.step_multiply
#print axioms AspisR1.NLC_Finish.step_original
#check @AspisR1.NLC_Finish.step_original
#print axioms AspisR1.NLC_Finish.step_payload2
#check @AspisR1.NLC_Finish.step_payload2
#print axioms AspisR1.NLC_Finish.step_record25a
#check @AspisR1.NLC_Finish.step_record25a
#print axioms AspisR1.NLC_Finish.step_record25b
#check @AspisR1.NLC_Finish.step_record25b
#print axioms AspisR1.NLC_Finish.step_record26a
#check @AspisR1.NLC_Finish.step_record26a
#print axioms AspisR1.NLC_Finish.step_record26b
#check @AspisR1.NLC_Finish.step_record26b
#print axioms AspisR1.NLC_Finish.step_rootCopy
#check @AspisR1.NLC_Finish.step_rootCopy
#print axioms AspisR1.NLC_Finish.step_rounds
#check @AspisR1.NLC_Finish.step_rounds
#print axioms AspisR1.NLC_Finish.step_stateBefore
#check @AspisR1.NLC_Finish.step_stateBefore
#print axioms AspisR1.NLC_Finish.step_terminal
#check @AspisR1.NLC_Finish.step_terminal
#print axioms AspisR1.NLC_Finish.step_terminalGuard
#check @AspisR1.NLC_Finish.step_terminalGuard
#print axioms AspisR1.NLC_Finish.step_verified
#check @AspisR1.NLC_Finish.step_verified
#print axioms AspisR1.NLC_Finish.verified_final
#check @AspisR1.NLC_Finish.verified_final
#print axioms AspisR1.NLC_MapCut.model
#check @AspisR1.NLC_MapCut.model
#print axioms AspisR1.NLC_MapCut.to_source
#check @AspisR1.NLC_MapCut.to_source
