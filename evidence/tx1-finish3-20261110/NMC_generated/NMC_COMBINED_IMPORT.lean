import NLS_COMBINED_IMPORT
import NLU_COMBINED_IMPORT
import NLI_COMBINED_IMPORT
import NLH_COMBINED_IMPORT
import NMC_AllSlotFrame
import NMC_AllSlotFrames
import NMC_ClaimsSegment
import NMC_Cut_blind
import NMC_Cut_circleGuard
import NMC_Cut_decode25
import NMC_Cut_decode26
import NMC_Cut_extra28
import NMC_Cut_high
import NMC_Cut_low
import NMC_Cut_mapPublic
import NMC_Cut_stateBefore
import NMC_Cut_terminalGuard
import NMC_EraseBind
import NMC_ErrorExit
import NMC_FrameComplete
import NMC_FrameProjections
import NMC_GuardReflect
import NMC_HeapLaws
import NMC_LocalWindows
import NMC_OriginWrites
import NMC_Origins
import NMC_ParentState
import NMC_PartialFrames
import NMC_ReachableOrigins
import NMC_RecordAtState
import NMC_RecordOrigins
import NMC_RecordPreserved
import NMC_RecordWrites
import NMC_RegionFrames
import NMC_RootComplement
import NMC_RootStages
import NMC_SlotFrame_addExtra
import NMC_SlotFrame_addMask
import NMC_SlotFrame_alpha
import NMC_SlotFrame_blind
import NMC_SlotFrame_circle0
import NMC_SlotFrame_circle1
import NMC_SlotFrame_circleGuard
import NMC_SlotFrame_claims
import NMC_SlotFrame_decode25
import NMC_SlotFrame_decode26
import NMC_SlotFrame_extra28
import NMC_SlotFrame_highArray
import NMC_SlotFrame_lowArray
import NMC_SlotFrame_mapPublic
import NMC_SlotFrame_mark2
import NMC_SlotFrame_mark3
import NMC_SlotFrame_mark4
import NMC_SlotFrame_mark5
import NMC_SlotFrame_mask
import NMC_SlotFrame_multiply
import NMC_SlotFrame_original
import NMC_SlotFrame_payload2
import NMC_SlotFrame_record25a
import NMC_SlotFrame_record25b
import NMC_SlotFrame_record26a
import NMC_SlotFrame_record26b
import NMC_SlotFrame_rootCopy
import NMC_SlotFrame_rounds
import NMC_SlotFrame_stateBefore
import NMC_SlotFrame_terminal
import NMC_SlotFrame_terminalGuard
import NMC_SlotFrame_verified
import NMC_TerminalAtState
import NMC_TerminalSegment
import NMC_Transcription
import NMC_ValueFrame
import NMC_WindowModels

-- SUPPORT ONLY; no full136 fold/root or ledger credit.
#print axioms AspisR1.RPx_Deployed.deployed
#check @AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NMC_Claims.abort
#check @AspisR1.NMC_Claims.abort
#print axioms AspisR1.NMC_Claims.frame
#check @AspisR1.NMC_Claims.frame
#print axioms AspisR1.NMC_Claims.installed
#check @AspisR1.NMC_Claims.installed
#print axioms AspisR1.NMC_Code.erase_bind
#check @AspisR1.NMC_Code.erase_bind
#print axioms AspisR1.NMC_Compare.emitted_eq
#check @AspisR1.NMC_Compare.emitted_eq
#print axioms AspisR1.NMC_Compare.peq_true
#check @AspisR1.NMC_Compare.peq_true
#print axioms AspisR1.NMC_Compare.qeq_true
#check @AspisR1.NMC_Compare.qeq_true
#print axioms AspisR1.NMC_Cut_blind.forward
#check @AspisR1.NMC_Cut_blind.forward
#print axioms AspisR1.NMC_Cut_circleGuard.forward
#check @AspisR1.NMC_Cut_circleGuard.forward
#print axioms AspisR1.NMC_Cut_decode25.forward
#check @AspisR1.NMC_Cut_decode25.forward
#print axioms AspisR1.NMC_Cut_decode26.forward
#check @AspisR1.NMC_Cut_decode26.forward
#print axioms AspisR1.NMC_Cut_extra28.forward
#check @AspisR1.NMC_Cut_extra28.forward
#print axioms AspisR1.NMC_Cut_high.forward
#check @AspisR1.NMC_Cut_high.forward
#print axioms AspisR1.NMC_Cut_low.forward
#check @AspisR1.NMC_Cut_low.forward
#print axioms AspisR1.NMC_Cut_mapPublic.forward
#check @AspisR1.NMC_Cut_mapPublic.forward
#print axioms AspisR1.NMC_Cut_stateBefore.forward
#check @AspisR1.NMC_Cut_stateBefore.forward
#print axioms AspisR1.NMC_Cut_terminalGuard.forward
#check @AspisR1.NMC_Cut_terminalGuard.forward
#print axioms AspisR1.NMC_Exit.cleanup_abort
#check @AspisR1.NMC_Exit.cleanup_abort
#print axioms AspisR1.NMC_Exit.cleanup_frame
#check @AspisR1.NMC_Exit.cleanup_frame
#print axioms AspisR1.NMC_Exit.public_abort
#check @AspisR1.NMC_Exit.public_abort
#print axioms AspisR1.NMC_Frame.alpha
#check @AspisR1.NMC_Frame.alpha
#print axioms AspisR1.NMC_Frame.before
#check @AspisR1.NMC_Frame.before
#print axioms AspisR1.NMC_Frame.challenge_ext
#check @AspisR1.NMC_Frame.challenge_ext
#print axioms AspisR1.NMC_Frame.challenges_chi
#check @AspisR1.NMC_Frame.challenges_chi
#print axioms AspisR1.NMC_Frame.challenges_eta
#check @AspisR1.NMC_Frame.challenges_eta
#print axioms AspisR1.NMC_Frame.challenges_lambda
#check @AspisR1.NMC_Frame.challenges_lambda
#print axioms AspisR1.NMC_Frame.challenges_mu
#check @AspisR1.NMC_Frame.challenges_mu
#print axioms AspisR1.NMC_Frame.challenges_theta
#check @AspisR1.NMC_Frame.challenges_theta
#print axioms AspisR1.NMC_Frame.challenges_zc
#check @AspisR1.NMC_Frame.challenges_zc
#print axioms AspisR1.NMC_Frame.claims_identity
#check @AspisR1.NMC_Frame.claims_identity
#print axioms AspisR1.NMC_Frame.claims_value
#check @AspisR1.NMC_Frame.claims_value
#print axioms AspisR1.NMC_Frame.complete
#check @AspisR1.NMC_Frame.complete
#print axioms AspisR1.NMC_Frame.extra
#check @AspisR1.NMC_Frame.extra
#print axioms AspisR1.NMC_Frame.mask
#check @AspisR1.NMC_Frame.mask
#print axioms AspisR1.NMC_Frame.owned_ext
#check @AspisR1.NMC_Frame.owned_ext
#print axioms AspisR1.NMC_Frame.point_ext
#check @AspisR1.NMC_Frame.point_ext
#print axioms AspisR1.NMC_Frame.reservation
#check @AspisR1.NMC_Frame.reservation
#print axioms AspisR1.NMC_Frame.rest
#check @AspisR1.NMC_Frame.rest
#print axioms AspisR1.NMC_Frame.running
#check @AspisR1.NMC_Frame.running
#print axioms AspisR1.NMC_Frame.state
#check @AspisR1.NMC_Frame.state
#print axioms AspisR1.NMC_Frame.terminal
#check @AspisR1.NMC_Frame.terminal
#print axioms AspisR1.NMC_Frame.transcript_ext
#check @AspisR1.NMC_Frame.transcript_ext
#print axioms AspisR1.NMC_Frame.transcript_next
#check @AspisR1.NMC_Frame.transcript_next
#print axioms AspisR1.NMC_Frame.transcript_state
#check @AspisR1.NMC_Frame.transcript_state
#print axioms AspisR1.NMC_Frame.value_ext
#check @AspisR1.NMC_Frame.value_ext
#print axioms AspisR1.NMC_Frame.z0_x
#check @AspisR1.NMC_Frame.z0_x
#print axioms AspisR1.NMC_Frame.z0_y
#check @AspisR1.NMC_Frame.z0_y
#print axioms AspisR1.NMC_Frame.z1_x
#check @AspisR1.NMC_Frame.z1_x
#print axioms AspisR1.NMC_Frame.z1_y
#check @AspisR1.NMC_Frame.z1_y
#print axioms AspisR1.NMC_Origins.alpha_preserved
#check @AspisR1.NMC_Origins.alpha_preserved
#print axioms AspisR1.NMC_Origins.alpha_written
#check @AspisR1.NMC_Origins.alpha_written
#print axioms AspisR1.NMC_Origins.claims_preserved
#check @AspisR1.NMC_Origins.claims_preserved
#print axioms AspisR1.NMC_Origins.claims_written
#check @AspisR1.NMC_Origins.claims_written
#print axioms AspisR1.NMC_Origins.initial_alpha
#check @AspisR1.NMC_Origins.initial_alpha
#print axioms AspisR1.NMC_Origins.initial_claims
#check @AspisR1.NMC_Origins.initial_claims
#print axioms AspisR1.NMC_Origins.reachable
#check @AspisR1.NMC_Origins.reachable
#print axioms AspisR1.NMC_Parent.claims_layout
#check @AspisR1.NMC_Parent.claims_layout
#print axioms AspisR1.NMC_Parent.owned_value
#check @AspisR1.NMC_Parent.owned_value
#print axioms AspisR1.NMC_Parent.raw_frame
#check @AspisR1.NMC_Parent.raw_frame
#print axioms AspisR1.NMC_Parent.release_frame
#check @AspisR1.NMC_Parent.release_frame
#print axioms AspisR1.NMC_Parent.write_frame
#check @AspisR1.NMC_Parent.write_frame
#print axioms AspisR1.NMC_Parent.write_owner
#check @AspisR1.NMC_Parent.write_owner
#print axioms AspisR1.NMC_Partial.advance
#check @AspisR1.NMC_Partial.advance
#print axioms AspisR1.NMC_Partial.write_cell
#check @AspisR1.NMC_Partial.write_cell
#print axioms AspisR1.NMC_Partial.write_frame
#check @AspisR1.NMC_Partial.write_frame
#print axioms AspisR1.NMC_Partial.write_identity
#check @AspisR1.NMC_Partial.write_identity
#print axioms AspisR1.NMC_Records.circle0
#check @AspisR1.NMC_Records.circle0
#print axioms AspisR1.NMC_Records.circle1
#check @AspisR1.NMC_Records.circle1
#print axioms AspisR1.NMC_Records.decode25
#check @AspisR1.NMC_Records.decode25
#print axioms AspisR1.NMC_Records.decode26
#check @AspisR1.NMC_Records.decode26
#print axioms AspisR1.NMC_Records.preserve25
#check @AspisR1.NMC_Records.preserve25
#print axioms AspisR1.NMC_Records.preserve26
#check @AspisR1.NMC_Records.preserve26
#print axioms AspisR1.NMC_Records.reachable
#check @AspisR1.NMC_Records.reachable
#print axioms AspisR1.NMC_Records.record25a
#check @AspisR1.NMC_Records.record25a
#print axioms AspisR1.NMC_Records.record25b
#check @AspisR1.NMC_Records.record25b
#print axioms AspisR1.NMC_Records.record26a
#check @AspisR1.NMC_Records.record26a
#print axioms AspisR1.NMC_Records.record26b
#check @AspisR1.NMC_Records.record26b
#print axioms AspisR1.NMC_Records.some_slot
#check @AspisR1.NMC_Records.some_slot
#print axioms AspisR1.NMC_Records.unique
#check @AspisR1.NMC_Records.unique
#print axioms AspisR1.NMC_Records.written
#check @AspisR1.NMC_Records.written
#print axioms AspisR1.NMC_Root.exact_length
#check @AspisR1.NMC_Root.exact_length
#print axioms AspisR1.NMC_Root.wrong_length
#check @AspisR1.NMC_Root.wrong_length
#print axioms AspisR1.NMC_RootStages.abort_frontier
#check @AspisR1.NMC_RootStages.abort_frontier
#print axioms AspisR1.NMC_RootStages.wrong_length
#check @AspisR1.NMC_RootStages.wrong_length
#print axioms AspisR1.NMC_Slots.all_frames
#check @AspisR1.NMC_Slots.all_frames
#print axioms AspisR1.NMC_Slots.frame_addExtra
#check @AspisR1.NMC_Slots.frame_addExtra
#print axioms AspisR1.NMC_Slots.frame_addMask
#check @AspisR1.NMC_Slots.frame_addMask
#print axioms AspisR1.NMC_Slots.frame_alpha
#check @AspisR1.NMC_Slots.frame_alpha
#print axioms AspisR1.NMC_Slots.frame_blind
#check @AspisR1.NMC_Slots.frame_blind
#print axioms AspisR1.NMC_Slots.frame_circle0
#check @AspisR1.NMC_Slots.frame_circle0
#print axioms AspisR1.NMC_Slots.frame_circle1
#check @AspisR1.NMC_Slots.frame_circle1
#print axioms AspisR1.NMC_Slots.frame_circleGuard
#check @AspisR1.NMC_Slots.frame_circleGuard
#print axioms AspisR1.NMC_Slots.frame_claims
#check @AspisR1.NMC_Slots.frame_claims
#print axioms AspisR1.NMC_Slots.frame_decode25
#check @AspisR1.NMC_Slots.frame_decode25
#print axioms AspisR1.NMC_Slots.frame_decode26
#check @AspisR1.NMC_Slots.frame_decode26
#print axioms AspisR1.NMC_Slots.frame_extra28
#check @AspisR1.NMC_Slots.frame_extra28
#print axioms AspisR1.NMC_Slots.frame_highArray
#check @AspisR1.NMC_Slots.frame_highArray
#print axioms AspisR1.NMC_Slots.frame_lowArray
#check @AspisR1.NMC_Slots.frame_lowArray
#print axioms AspisR1.NMC_Slots.frame_mapPublic
#check @AspisR1.NMC_Slots.frame_mapPublic
#print axioms AspisR1.NMC_Slots.frame_mark2
#check @AspisR1.NMC_Slots.frame_mark2
#print axioms AspisR1.NMC_Slots.frame_mark3
#check @AspisR1.NMC_Slots.frame_mark3
#print axioms AspisR1.NMC_Slots.frame_mark4
#check @AspisR1.NMC_Slots.frame_mark4
#print axioms AspisR1.NMC_Slots.frame_mark5
#check @AspisR1.NMC_Slots.frame_mark5
#print axioms AspisR1.NMC_Slots.frame_mask
#check @AspisR1.NMC_Slots.frame_mask
#print axioms AspisR1.NMC_Slots.frame_multiply
#check @AspisR1.NMC_Slots.frame_multiply
#print axioms AspisR1.NMC_Slots.frame_original
#check @AspisR1.NMC_Slots.frame_original
#print axioms AspisR1.NMC_Slots.frame_payload2
#check @AspisR1.NMC_Slots.frame_payload2
#print axioms AspisR1.NMC_Slots.frame_record25a
#check @AspisR1.NMC_Slots.frame_record25a
#print axioms AspisR1.NMC_Slots.frame_record25b
#check @AspisR1.NMC_Slots.frame_record25b
#print axioms AspisR1.NMC_Slots.frame_record26a
#check @AspisR1.NMC_Slots.frame_record26a
#print axioms AspisR1.NMC_Slots.frame_record26b
#check @AspisR1.NMC_Slots.frame_record26b
#print axioms AspisR1.NMC_Slots.frame_rootCopy
#check @AspisR1.NMC_Slots.frame_rootCopy
#print axioms AspisR1.NMC_Slots.frame_rounds
#check @AspisR1.NMC_Slots.frame_rounds
#print axioms AspisR1.NMC_Slots.frame_stateBefore
#check @AspisR1.NMC_Slots.frame_stateBefore
#print axioms AspisR1.NMC_Slots.frame_terminal
#check @AspisR1.NMC_Slots.frame_terminal
#print axioms AspisR1.NMC_Slots.frame_terminalGuard
#check @AspisR1.NMC_Slots.frame_terminalGuard
#print axioms AspisR1.NMC_Slots.frame_verified
#check @AspisR1.NMC_Slots.frame_verified
#print axioms AspisR1.NMC_Slots.next
#check @AspisR1.NMC_Slots.next
#print axioms AspisR1.NMC_Slots.put
#check @AspisR1.NMC_Slots.put
#print axioms AspisR1.NMC_Slots.returned
#check @AspisR1.NMC_Slots.returned
#print axioms AspisR1.NMC_Slots.source_frame
#check @AspisR1.NMC_Slots.source_frame
#print axioms AspisR1.NMC_Terminal.actual_arguments
#check @AspisR1.NMC_Terminal.actual_arguments
#print axioms AspisR1.NMC_Terminal.installed
#check @AspisR1.NMC_Terminal.installed
#print axioms AspisR1.NMC_Transcription.source
#check @AspisR1.NMC_Transcription.source
#print axioms AspisR1.NMC_Window.context_ext
#check @AspisR1.NMC_Window.context_ext
#print axioms AspisR1.NMC_Window.from_windows
#check @AspisR1.NMC_Window.from_windows
#print axioms AspisR1.NMC_Window.observation_ext
#check @AspisR1.NMC_Window.observation_ext
