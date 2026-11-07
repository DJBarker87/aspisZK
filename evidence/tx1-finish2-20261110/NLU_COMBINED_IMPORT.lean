import NLO_COMBINED_IMPORT
import NLI_COMBINED_IMPORT
import NLC_COMBINED_IMPORT
import NLH_COMBINED_IMPORT
import NLU_Action
import NLU_Arithmetic
import NLU_CanonicalTransport
import NLU_Cell
import NLU_CircleDomains
import NLU_ClaimsCanonical
import NLU_ClaimsInstall
import NLU_ConstructArrays
import NLU_ConstructChallenges
import NLU_ConstructComplete
import NLU_ConstructCut
import NLU_ConstructMisc
import NLU_ConstructPoints
import NLU_ConstructTranscript
import NLU_DecodeDomains
import NLU_EventProjection
import NLU_Execute
import NLU_FieldLog
import NLU_FieldValues
import NLU_Fold
import NLU_FoldProjection
import NLU_Frontier
import NLU_FrontierSource
import NLU_GeneratedMul
import NLU_Head_addExtra
import NLU_Head_addMask
import NLU_Head_alpha
import NLU_Head_blind
import NLU_Head_circle0
import NLU_Head_circle1
import NLU_Head_circleGuard
import NLU_Head_claims
import NLU_Head_decode25
import NLU_Head_decode26
import NLU_Head_extra28
import NLU_Head_highArray
import NLU_Head_highIndex
import NLU_Head_lowArray
import NLU_Head_lowIndex
import NLU_Head_mapPublic
import NLU_Head_mark2
import NLU_Head_mark3
import NLU_Head_mark4
import NLU_Head_mark5
import NLU_Head_mask
import NLU_Head_multiply
import NLU_Head_original
import NLU_Head_payload2
import NLU_Head_record25a
import NLU_Head_record25b
import NLU_Head_record26a
import NLU_Head_record26b
import NLU_Head_rootCopy
import NLU_Head_rounds
import NLU_Head_stateBefore
import NLU_Head_terminal
import NLU_Head_terminalGuard
import NLU_Head_verified
import NLU_HighCut
import NLU_HighLoop
import NLU_InputDomain
import NLU_Invariant
import NLU_Linear
import NLU_Nested
import NLU_Next
import NLU_SameTerminal
import NLU_SlotFrame
import NLU_SlotFrame0
import NLU_SlotFrame1
import NLU_SlotFrame2
import NLU_SlotFrame3
import NLU_SlotFrame4
import NLU_SlotFrames
import NLU_SourceProjection
import NLU_State
import NLU_StatementAudit
import NLU_StepProjection
import NLU_TerminalCanonical
import NLU_TerminalDomain
import NLU_TerminalTransport
import NLU_Verified
import NLU_Words

-- Support gate only; no136 native root or ledger credit is implied.
#print axioms AspisR1.RPx_Deployed.deployed
#check @AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NLU.carry_digest
#check @AspisR1.NLU.carry_digest
#print axioms AspisR1.NLU.carry_projection
#check @AspisR1.NLU.carry_projection
#print axioms AspisR1.NLU.cells_ext
#check @AspisR1.NLU.cells_ext
#print axioms AspisR1.NLU.claims_rank
#check @AspisR1.NLU.claims_rank
#print axioms AspisR1.NLU.continuation_linear
#check @AspisR1.NLU.continuation_linear
#print axioms AspisR1.NLU.digest_append
#check @AspisR1.NLU.digest_append
#print axioms AspisR1.NLU.entered_digest
#check @AspisR1.NLU.entered_digest
#print axioms AspisR1.NLU.execute_step
#check @AspisR1.NLU.execute_step
#print axioms AspisR1.NLU.fold_projection
#check @AspisR1.NLU.fold_projection
#print axioms AspisR1.NLU.high_arguments
#check @AspisR1.NLU.high_arguments
#print axioms AspisR1.NLU.initial_invariant
#check @AspisR1.NLU.initial_invariant
#print axioms AspisR1.NLU.initial_linear
#check @AspisR1.NLU.initial_linear
#print axioms AspisR1.NLU.low_arguments
#check @AspisR1.NLU.low_arguments
#print axioms AspisR1.NLU.map_digest
#check @AspisR1.NLU.map_digest
#print axioms AspisR1.NLU.next_characterization
#check @AspisR1.NLU.next_characterization
#print axioms AspisR1.NLU.next_input
#check @AspisR1.NLU.next_input
#print axioms AspisR1.NLU.next_invariant
#check @AspisR1.NLU.next_invariant
#print axioms AspisR1.NLU.next_linear
#check @AspisR1.NLU.next_linear
#print axioms AspisR1.NLU.parsed_of_domain
#check @AspisR1.NLU.parsed_of_domain
#print axioms AspisR1.NLU.reachable_invariant
#check @AspisR1.NLU.reachable_invariant
#print axioms AspisR1.NLU.root_occurrences
#check @AspisR1.NLU.root_occurrences
#print axioms AspisR1.NLU.some_of_initialized
#check @AspisR1.NLU.some_of_initialized
#print axioms AspisR1.NLU.source_projection
#check @AspisR1.NLU.source_projection
#print axioms AspisR1.NLU.step_digest
#check @AspisR1.NLU.step_digest
#print axioms AspisR1.NLU.step_input
#check @AspisR1.NLU.step_input
#print axioms AspisR1.NLU.step_projection
#check @AspisR1.NLU.step_projection
#print axioms AspisR1.NLU.verified_constructed
#check @AspisR1.NLU.verified_constructed
#print axioms AspisR1.NLU.word_ext
#check @AspisR1.NLU.word_ext
#print axioms AspisR1.NLU_Arithmetic.source
#check @AspisR1.NLU_Arithmetic.source
#print axioms AspisR1.NLU_Circle.source
#check @AspisR1.NLU_Circle.source
#print axioms AspisR1.NLU_Claims.source
#check @AspisR1.NLU_Claims.source
#print axioms AspisR1.NLU_Construct.alpha
#check @AspisR1.NLU_Construct.alpha
#print axioms AspisR1.NLU_Construct.before
#check @AspisR1.NLU_Construct.before
#print axioms AspisR1.NLU_Construct.challenges
#check @AspisR1.NLU_Construct.challenges
#print axioms AspisR1.NLU_Construct.claims
#check @AspisR1.NLU_Construct.claims
#print axioms AspisR1.NLU_Construct.complete
#check @AspisR1.NLU_Construct.complete
#print axioms AspisR1.NLU_Construct.extra
#check @AspisR1.NLU_Construct.extra
#print axioms AspisR1.NLU_Construct.point_ext
#check @AspisR1.NLU_Construct.point_ext
#print axioms AspisR1.NLU_Construct.points
#check @AspisR1.NLU_Construct.points
#print axioms AspisR1.NLU_Construct.roots
#check @AspisR1.NLU_Construct.roots
#print axioms AspisR1.NLU_Construct.state
#check @AspisR1.NLU_Construct.state
#print axioms AspisR1.NLU_Construct.transcript
#check @AspisR1.NLU_Construct.transcript
#print axioms AspisR1.NLU_Construct.transcript_ext
#check @AspisR1.NLU_Construct.transcript_ext
#print axioms AspisR1.NLU_Construct.value_ext
#check @AspisR1.NLU_Construct.value_ext
#print axioms AspisR1.NLU_Decode.source
#check @AspisR1.NLU_Decode.source
#print axioms AspisR1.NLU_FieldLog.complete
#check @AspisR1.NLU_FieldLog.complete
#print axioms AspisR1.NLU_FieldLog.operands
#check @AspisR1.NLU_FieldLog.operands
#print axioms AspisR1.NLU_FieldLog.returned
#check @AspisR1.NLU_FieldLog.returned
#print axioms AspisR1.NLU_FieldValues.add_transport
#check @AspisR1.NLU_FieldValues.add_transport
#print axioms AspisR1.NLU_FieldValues.add_value
#check @AspisR1.NLU_FieldValues.add_value
#print axioms AspisR1.NLU_FieldValues.mul_transport
#check @AspisR1.NLU_FieldValues.mul_transport
#print axioms AspisR1.NLU_FieldValues.mul_value
#check @AspisR1.NLU_FieldValues.mul_value
#print axioms AspisR1.NLU_Frontier.initialized_frontier
#check @AspisR1.NLU_Frontier.initialized_frontier
#print axioms AspisR1.NLU_Frontier.reached
#check @AspisR1.NLU_Frontier.reached
#print axioms AspisR1.NLU_Frontier.source
#check @AspisR1.NLU_Frontier.source
#print axioms AspisR1.NLU_Frontier.summary
#check @AspisR1.NLU_Frontier.summary
#print axioms AspisR1.NLU_Generated.emitted_mul
#check @AspisR1.NLU_Generated.emitted_mul
#print axioms AspisR1.NLU_Heads.source_addExtra
#check @AspisR1.NLU_Heads.source_addExtra
#print axioms AspisR1.NLU_Heads.source_addMask
#check @AspisR1.NLU_Heads.source_addMask
#print axioms AspisR1.NLU_Heads.source_alpha
#check @AspisR1.NLU_Heads.source_alpha
#print axioms AspisR1.NLU_Heads.source_blind
#check @AspisR1.NLU_Heads.source_blind
#print axioms AspisR1.NLU_Heads.source_circle0
#check @AspisR1.NLU_Heads.source_circle0
#print axioms AspisR1.NLU_Heads.source_circle1
#check @AspisR1.NLU_Heads.source_circle1
#print axioms AspisR1.NLU_Heads.source_circleGuard
#check @AspisR1.NLU_Heads.source_circleGuard
#print axioms AspisR1.NLU_Heads.source_claims
#check @AspisR1.NLU_Heads.source_claims
#print axioms AspisR1.NLU_Heads.source_decode25
#check @AspisR1.NLU_Heads.source_decode25
#print axioms AspisR1.NLU_Heads.source_decode26
#check @AspisR1.NLU_Heads.source_decode26
#print axioms AspisR1.NLU_Heads.source_extra28
#check @AspisR1.NLU_Heads.source_extra28
#print axioms AspisR1.NLU_Heads.source_highArray
#check @AspisR1.NLU_Heads.source_highArray
#print axioms AspisR1.NLU_Heads.source_highIndex
#check @AspisR1.NLU_Heads.source_highIndex
#print axioms AspisR1.NLU_Heads.source_lowArray
#check @AspisR1.NLU_Heads.source_lowArray
#print axioms AspisR1.NLU_Heads.source_lowIndex
#check @AspisR1.NLU_Heads.source_lowIndex
#print axioms AspisR1.NLU_Heads.source_mapPublic
#check @AspisR1.NLU_Heads.source_mapPublic
#print axioms AspisR1.NLU_Heads.source_mark2
#check @AspisR1.NLU_Heads.source_mark2
#print axioms AspisR1.NLU_Heads.source_mark3
#check @AspisR1.NLU_Heads.source_mark3
#print axioms AspisR1.NLU_Heads.source_mark4
#check @AspisR1.NLU_Heads.source_mark4
#print axioms AspisR1.NLU_Heads.source_mark5
#check @AspisR1.NLU_Heads.source_mark5
#print axioms AspisR1.NLU_Heads.source_mask
#check @AspisR1.NLU_Heads.source_mask
#print axioms AspisR1.NLU_Heads.source_multiply
#check @AspisR1.NLU_Heads.source_multiply
#print axioms AspisR1.NLU_Heads.source_original
#check @AspisR1.NLU_Heads.source_original
#print axioms AspisR1.NLU_Heads.source_payload2
#check @AspisR1.NLU_Heads.source_payload2
#print axioms AspisR1.NLU_Heads.source_record25a
#check @AspisR1.NLU_Heads.source_record25a
#print axioms AspisR1.NLU_Heads.source_record25b
#check @AspisR1.NLU_Heads.source_record25b
#print axioms AspisR1.NLU_Heads.source_record26a
#check @AspisR1.NLU_Heads.source_record26a
#print axioms AspisR1.NLU_Heads.source_record26b
#check @AspisR1.NLU_Heads.source_record26b
#print axioms AspisR1.NLU_Heads.source_rootCopy
#check @AspisR1.NLU_Heads.source_rootCopy
#print axioms AspisR1.NLU_Heads.source_rounds
#check @AspisR1.NLU_Heads.source_rounds
#print axioms AspisR1.NLU_Heads.source_stateBefore
#check @AspisR1.NLU_Heads.source_stateBefore
#print axioms AspisR1.NLU_Heads.source_terminal
#check @AspisR1.NLU_Heads.source_terminal
#print axioms AspisR1.NLU_Heads.source_terminalGuard
#check @AspisR1.NLU_Heads.source_terminalGuard
#print axioms AspisR1.NLU_Heads.source_verified
#check @AspisR1.NLU_Heads.source_verified
#print axioms AspisR1.NLU_High.complete
#check @AspisR1.NLU_High.complete
#print axioms AspisR1.NLU_High.frame
#check @AspisR1.NLU_High.frame
#print axioms AspisR1.NLU_High.induction
#check @AspisR1.NLU_High.induction
#print axioms AspisR1.NLU_High.initialized
#check @AspisR1.NLU_High.initialized
#print axioms AspisR1.NLU_High.value
#check @AspisR1.NLU_High.value
#print axioms AspisR1.NLU_Slots.all_frames
#check @AspisR1.NLU_Slots.all_frames
#print axioms AspisR1.NLU_Slots.frame_addExtra
#check @AspisR1.NLU_Slots.frame_addExtra
#print axioms AspisR1.NLU_Slots.frame_addMask
#check @AspisR1.NLU_Slots.frame_addMask
#print axioms AspisR1.NLU_Slots.frame_alpha
#check @AspisR1.NLU_Slots.frame_alpha
#print axioms AspisR1.NLU_Slots.frame_blind
#check @AspisR1.NLU_Slots.frame_blind
#print axioms AspisR1.NLU_Slots.frame_circle0
#check @AspisR1.NLU_Slots.frame_circle0
#print axioms AspisR1.NLU_Slots.frame_circle1
#check @AspisR1.NLU_Slots.frame_circle1
#print axioms AspisR1.NLU_Slots.frame_circleGuard
#check @AspisR1.NLU_Slots.frame_circleGuard
#print axioms AspisR1.NLU_Slots.frame_claims
#check @AspisR1.NLU_Slots.frame_claims
#print axioms AspisR1.NLU_Slots.frame_decode25
#check @AspisR1.NLU_Slots.frame_decode25
#print axioms AspisR1.NLU_Slots.frame_decode26
#check @AspisR1.NLU_Slots.frame_decode26
#print axioms AspisR1.NLU_Slots.frame_extra28
#check @AspisR1.NLU_Slots.frame_extra28
#print axioms AspisR1.NLU_Slots.frame_highArray
#check @AspisR1.NLU_Slots.frame_highArray
#print axioms AspisR1.NLU_Slots.frame_lowArray
#check @AspisR1.NLU_Slots.frame_lowArray
#print axioms AspisR1.NLU_Slots.frame_mapPublic
#check @AspisR1.NLU_Slots.frame_mapPublic
#print axioms AspisR1.NLU_Slots.frame_mark2
#check @AspisR1.NLU_Slots.frame_mark2
#print axioms AspisR1.NLU_Slots.frame_mark3
#check @AspisR1.NLU_Slots.frame_mark3
#print axioms AspisR1.NLU_Slots.frame_mark4
#check @AspisR1.NLU_Slots.frame_mark4
#print axioms AspisR1.NLU_Slots.frame_mark5
#check @AspisR1.NLU_Slots.frame_mark5
#print axioms AspisR1.NLU_Slots.frame_mask
#check @AspisR1.NLU_Slots.frame_mask
#print axioms AspisR1.NLU_Slots.frame_multiply
#check @AspisR1.NLU_Slots.frame_multiply
#print axioms AspisR1.NLU_Slots.frame_original
#check @AspisR1.NLU_Slots.frame_original
#print axioms AspisR1.NLU_Slots.frame_payload2
#check @AspisR1.NLU_Slots.frame_payload2
#print axioms AspisR1.NLU_Slots.frame_record25a
#check @AspisR1.NLU_Slots.frame_record25a
#print axioms AspisR1.NLU_Slots.frame_record25b
#check @AspisR1.NLU_Slots.frame_record25b
#print axioms AspisR1.NLU_Slots.frame_record26a
#check @AspisR1.NLU_Slots.frame_record26a
#print axioms AspisR1.NLU_Slots.frame_record26b
#check @AspisR1.NLU_Slots.frame_record26b
#print axioms AspisR1.NLU_Slots.frame_rootCopy
#check @AspisR1.NLU_Slots.frame_rootCopy
#print axioms AspisR1.NLU_Slots.frame_rounds
#check @AspisR1.NLU_Slots.frame_rounds
#print axioms AspisR1.NLU_Slots.frame_stateBefore
#check @AspisR1.NLU_Slots.frame_stateBefore
#print axioms AspisR1.NLU_Slots.frame_terminal
#check @AspisR1.NLU_Slots.frame_terminal
#print axioms AspisR1.NLU_Slots.frame_terminalGuard
#check @AspisR1.NLU_Slots.frame_terminalGuard
#print axioms AspisR1.NLU_Slots.frame_verified
#check @AspisR1.NLU_Slots.frame_verified
#print axioms AspisR1.NLU_Slots.next
#check @AspisR1.NLU_Slots.next
#print axioms AspisR1.NLU_Slots.put
#check @AspisR1.NLU_Slots.put
#print axioms AspisR1.NLU_Slots.returned
#check @AspisR1.NLU_Slots.returned
#print axioms AspisR1.NLU_Slots.source_frame
#check @AspisR1.NLU_Slots.source_frame
#print axioms AspisR1.NLU_Terminal.array_to_native
#check @AspisR1.NLU_Terminal.array_to_native
#print axioms AspisR1.NLU_Terminal.canonical_from_native
#check @AspisR1.NLU_Terminal.canonical_from_native
#print axioms AspisR1.NLU_Terminal.canonical_to_native
#check @AspisR1.NLU_Terminal.canonical_to_native
#print axioms AspisR1.NLU_Terminal.claims_domain
#check @AspisR1.NLU_Terminal.claims_domain
#print axioms AspisR1.NLU_Terminal.claims_to_native
#check @AspisR1.NLU_Terminal.claims_to_native
#print axioms AspisR1.NLU_Terminal.converted
#check @AspisR1.NLU_Terminal.converted
#print axioms AspisR1.NLU_Terminal.first_calls
#check @AspisR1.NLU_Terminal.first_calls
#print axioms AspisR1.NLU_Terminal.install
#check @AspisR1.NLU_Terminal.install
#print axioms AspisR1.NLU_Terminal.installed
#check @AspisR1.NLU_Terminal.installed
#print axioms AspisR1.NLU_Terminal.nkq_to_native
#check @AspisR1.NLU_Terminal.nkq_to_native
#print axioms AspisR1.NLU_Terminal.source
#check @AspisR1.NLU_Terminal.source
