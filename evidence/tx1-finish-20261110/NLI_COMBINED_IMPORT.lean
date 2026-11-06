import NLG_COMBINED_IMPORT
import NLC_COMBINED_IMPORT
import NLI_CallbackAssociation
import NLI_FoldPhase
import NLI_FoldTicks
import NLI_FromFnInduction
import NLI_FullRowSpec136
import NLI_LiftLaws
import NLI_Monad
import NLI_MonadNotation
import NLI_ParsedCase
import NLI_ResourceState
import NLI_ResourceStep
import NLI_RoundsCarry
import NLI_RoundsHash
import NLI_RoundsInstall
import NLI_RoundsWindows
import NLI_RowSpec136
import NLI_RowSpec256
import NLI_RunLaws
import NLI_SourceComparison
import NLI_SourceEquality
import NLI_Suffix_addExtra
import NLI_Suffix_addMask
import NLI_Suffix_alpha
import NLI_Suffix_blind
import NLI_Suffix_circle0
import NLI_Suffix_circle1
import NLI_Suffix_circleGuard
import NLI_Suffix_claims
import NLI_Suffix_decode25
import NLI_Suffix_decode26
import NLI_Suffix_extra28
import NLI_Suffix_highArray
import NLI_Suffix_lowArray
import NLI_Suffix_mapPublic
import NLI_Suffix_mark2
import NLI_Suffix_mark3
import NLI_Suffix_mark4
import NLI_Suffix_mark5
import NLI_Suffix_mask
import NLI_Suffix_multiply
import NLI_Suffix_original
import NLI_Suffix_payload2
import NLI_Suffix_record25a
import NLI_Suffix_record25b
import NLI_Suffix_record26a
import NLI_Suffix_record26b
import NLI_Suffix_rootCopy
import NLI_Suffix_rounds
import NLI_Suffix_stateBefore
import NLI_Suffix_terminal
import NLI_Suffix_terminalGuard
import NLI_TailRoot
import NLI_TailVerified
import NLI_TerminalStep
import NLI_ViewFrames
import NLI_Window_addExtra
import NLI_Window_addMask
import NLI_Window_blind
import NLI_Window_claims
import NLI_Window_decode25
import NLI_Window_extra28
import NLI_Window_highArray
import NLI_Window_lowArray
import NLI_Window_mapPublic
import NLI_Window_mask
import NLI_Window_multiply
import NLI_Window_record25a
import NLI_Window_rounds
import NLI_Window_terminal
import NLI_Window_terminalGuard

-- No row credit before next ledger gate; exact submitted scope in handoff.
#print axioms AspisR1.RPx_Deployed.deployed
#check @AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NLI_CallbackAssociation.high
#check @AspisR1.NLI_CallbackAssociation.high
#print axioms AspisR1.NLI_CallbackAssociation.low
#check @AspisR1.NLI_CallbackAssociation.low
#print axioms AspisR1.NLI_FoldPhase.mark4
#check @AspisR1.NLI_FoldPhase.mark4
#print axioms AspisR1.NLI_FoldTicks.alpha
#check @AspisR1.NLI_FoldTicks.alpha
#print axioms AspisR1.NLI_FoldTicks.mark2
#check @AspisR1.NLI_FoldTicks.mark2
#print axioms AspisR1.NLI_FoldTicks.mark3
#check @AspisR1.NLI_FoldTicks.mark3
#print axioms AspisR1.NLI_FoldTicks.original
#check @AspisR1.NLI_FoldTicks.original
#print axioms AspisR1.NLI_FromFn.byte_frame
#check @AspisR1.NLI_FromFn.byte_frame
#print axioms AspisR1.NLI_FromFn.fill_prefix
#check @AspisR1.NLI_FromFn.fill_prefix
#print axioms AspisR1.NLI_FromFn.write_prefix
#check @AspisR1.NLI_FromFn.write_prefix
#print axioms AspisR1.NLI_LiftLaws.congr_lift
#check @AspisR1.NLI_LiftLaws.congr_lift
#print axioms AspisR1.NLI_Monad.bind_assoc
#check @AspisR1.NLI_Monad.bind_assoc
#print axioms AspisR1.NLI_Monad.bind_done
#check @AspisR1.NLI_Monad.bind_done
#print axioms AspisR1.NLI_Notation.assoc
#check @AspisR1.NLI_Notation.assoc
#print axioms AspisR1.NLI_Notation.congr_bind
#check @AspisR1.NLI_Notation.congr_bind
#print axioms AspisR1.NLI_Notation.lift_ok
#check @AspisR1.NLI_Notation.lift_ok
#print axioms AspisR1.NLI_Notation.pure_left
#check @AspisR1.NLI_Notation.pure_left
#print axioms AspisR1.NLI_ParsedCase.success
#check @AspisR1.NLI_ParsedCase.success
#print axioms AspisR1.NLI_RoundsCarry.from_child
#check @AspisR1.NLI_RoundsCarry.from_child
#print axioms AspisR1.NLI_RoundsCarry.source
#check @AspisR1.NLI_RoundsCarry.source
#print axioms AspisR1.NLI_RoundsHash.chain
#check @AspisR1.NLI_RoundsHash.chain
#print axioms AspisR1.NLI_RoundsHash.source
#check @AspisR1.NLI_RoundsHash.source
#print axioms AspisR1.NLI_RoundsInstall.source
#check @AspisR1.NLI_RoundsInstall.source
#print axioms AspisR1.NLI_RoundsWindows.complete
#check @AspisR1.NLI_RoundsWindows.complete
#print axioms AspisR1.NLI_RunLaws.bind_congr
#check @AspisR1.NLI_RunLaws.bind_congr
#print axioms AspisR1.NLI_RunLaws.step_ok
#check @AspisR1.NLI_RunLaws.step_ok
#print axioms AspisR1.NLI_Source.addExtra
#check @AspisR1.NLI_Source.addExtra
#print axioms AspisR1.NLI_Source.addMask
#check @AspisR1.NLI_Source.addMask
#print axioms AspisR1.NLI_Source.alpha
#check @AspisR1.NLI_Source.alpha
#print axioms AspisR1.NLI_Source.blind
#check @AspisR1.NLI_Source.blind
#print axioms AspisR1.NLI_Source.circle0
#check @AspisR1.NLI_Source.circle0
#print axioms AspisR1.NLI_Source.circle1
#check @AspisR1.NLI_Source.circle1
#print axioms AspisR1.NLI_Source.circleGuard
#check @AspisR1.NLI_Source.circleGuard
#print axioms AspisR1.NLI_Source.claims
#check @AspisR1.NLI_Source.claims
#print axioms AspisR1.NLI_Source.decode25
#check @AspisR1.NLI_Source.decode25
#print axioms AspisR1.NLI_Source.decode26
#check @AspisR1.NLI_Source.decode26
#print axioms AspisR1.NLI_Source.extra28
#check @AspisR1.NLI_Source.extra28
#print axioms AspisR1.NLI_Source.finishSourceEquality
#check @AspisR1.NLI_Source.finishSourceEquality
#print axioms AspisR1.NLI_Source.highArray
#check @AspisR1.NLI_Source.highArray
#print axioms AspisR1.NLI_Source.initialized_finish
#check @AspisR1.NLI_Source.initialized_finish
#print axioms AspisR1.NLI_Source.lowArray
#check @AspisR1.NLI_Source.lowArray
#print axioms AspisR1.NLI_Source.mapPublic
#check @AspisR1.NLI_Source.mapPublic
#print axioms AspisR1.NLI_Source.mark2
#check @AspisR1.NLI_Source.mark2
#print axioms AspisR1.NLI_Source.mark3
#check @AspisR1.NLI_Source.mark3
#print axioms AspisR1.NLI_Source.mark4
#check @AspisR1.NLI_Source.mark4
#print axioms AspisR1.NLI_Source.mark5
#check @AspisR1.NLI_Source.mark5
#print axioms AspisR1.NLI_Source.mask
#check @AspisR1.NLI_Source.mask
#print axioms AspisR1.NLI_Source.multiply
#check @AspisR1.NLI_Source.multiply
#print axioms AspisR1.NLI_Source.original
#check @AspisR1.NLI_Source.original
#print axioms AspisR1.NLI_Source.payload2
#check @AspisR1.NLI_Source.payload2
#print axioms AspisR1.NLI_Source.record25a
#check @AspisR1.NLI_Source.record25a
#print axioms AspisR1.NLI_Source.record25b
#check @AspisR1.NLI_Source.record25b
#print axioms AspisR1.NLI_Source.record26a
#check @AspisR1.NLI_Source.record26a
#print axioms AspisR1.NLI_Source.record26b
#check @AspisR1.NLI_Source.record26b
#print axioms AspisR1.NLI_Source.rootCopy
#check @AspisR1.NLI_Source.rootCopy
#print axioms AspisR1.NLI_Source.rootCopy_uniform
#check @AspisR1.NLI_Source.rootCopy_uniform
#print axioms AspisR1.NLI_Source.rounds
#check @AspisR1.NLI_Source.rounds
#print axioms AspisR1.NLI_Source.stateBefore
#check @AspisR1.NLI_Source.stateBefore
#print axioms AspisR1.NLI_Source.suffix_eq_finish
#check @AspisR1.NLI_Source.suffix_eq_finish
#print axioms AspisR1.NLI_Source.terminal
#check @AspisR1.NLI_Source.terminal
#print axioms AspisR1.NLI_Source.terminalGuard
#check @AspisR1.NLI_Source.terminalGuard
#print axioms AspisR1.NLI_Source.verified
#check @AspisR1.NLI_Source.verified
#print axioms AspisR1.NLI_TerminalStep.reply_exact
#check @AspisR1.NLI_TerminalStep.reply_exact
#print axioms AspisR1.NLI_TerminalStep.to_source
#check @AspisR1.NLI_TerminalStep.to_source
#print axioms AspisR1.NLI_ViewFrames.bounded_family_frame
#check @AspisR1.NLI_ViewFrames.bounded_family_frame
#print axioms AspisR1.NLI_ViewFrames.disjoint_copy_frame
#check @AspisR1.NLI_ViewFrames.disjoint_copy_frame
#print axioms AspisR1.NLI_ViewFrames.family_frame
#check @AspisR1.NLI_ViewFrames.family_frame
#print axioms AspisR1.NLI_ViewFrames.realized_frame
#check @AspisR1.NLI_ViewFrames.realized_frame
#print axioms AspisR1.NLI_Window.addExtra_head
#check @AspisR1.NLI_Window.addExtra_head
#print axioms AspisR1.NLI_Window.addMask_head
#check @AspisR1.NLI_Window.addMask_head
#print axioms AspisR1.NLI_Window.blind_head
#check @AspisR1.NLI_Window.blind_head
#print axioms AspisR1.NLI_Window.claims_head
#check @AspisR1.NLI_Window.claims_head
#print axioms AspisR1.NLI_Window.decode25_head
#check @AspisR1.NLI_Window.decode25_head
#print axioms AspisR1.NLI_Window.extra28_head
#check @AspisR1.NLI_Window.extra28_head
#print axioms AspisR1.NLI_Window.highArray_head
#check @AspisR1.NLI_Window.highArray_head
#print axioms AspisR1.NLI_Window.lowArray_head
#check @AspisR1.NLI_Window.lowArray_head
#print axioms AspisR1.NLI_Window.mapPublic_head
#check @AspisR1.NLI_Window.mapPublic_head
#print axioms AspisR1.NLI_Window.mask_head
#check @AspisR1.NLI_Window.mask_head
#print axioms AspisR1.NLI_Window.multiply_head
#check @AspisR1.NLI_Window.multiply_head
#print axioms AspisR1.NLI_Window.record25a_head
#check @AspisR1.NLI_Window.record25a_head
#print axioms AspisR1.NLI_Window.rounds_head
#check @AspisR1.NLI_Window.rounds_head
#print axioms AspisR1.NLI_Window.terminalGuard_head
#check @AspisR1.NLI_Window.terminalGuard_head
#print axioms AspisR1.NLI_Window.terminal_head
#check @AspisR1.NLI_Window.terminal_head
