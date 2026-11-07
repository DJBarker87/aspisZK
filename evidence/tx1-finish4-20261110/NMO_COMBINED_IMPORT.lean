import NLX_COMBINED_IMPORT
import NMC_COMBINED_IMPORT
import NLU_COMBINED_IMPORT
import NLI_COMBINED_IMPORT
import NLH_COMBINED_IMPORT
import NMO_ArithmeticAtState
import NMO_ArithmeticFold
import NMO_ArithmeticValue
import NMO_ArrayReachable
import NMO_ArrayStored
import NMO_BlindStored
import NMO_ChallengeWindows
import NMO_ClaimsAtState
import NMO_ConstructorMemory
import NMO_ErrorFrontier
import NMO_ExtraCell
import NMO_ExtraStored
import NMO_ExtraValue
import NMO_MapStored
import NMO_MaskAtState
import NMO_MaskStored
import NMO_MaskValue
import NMO_MulAtState
import NMO_PrefixBounds
import NMO_PrefixErrors
import NMO_TerminalStored
import NMO_TerminalWindows
import NMO_Transcription

-- SUPPORT GATE ONLY: TX1:136 has no candidate root.
#print axioms AspisR1.RPx_Deployed.deployed
#check @AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NMO_ArithmeticAtState.source
#check @AspisR1.NMO_ArithmeticAtState.source
#print axioms AspisR1.NMO_ArithmeticFold.source
#check @AspisR1.NMO_ArithmeticFold.source
#print axioms AspisR1.NMO_ArithmeticValue.source
#check @AspisR1.NMO_ArithmeticValue.source
#print axioms AspisR1.NMO_ArrayStored.blind_preserved
#check @AspisR1.NMO_ArrayStored.blind_preserved
#print axioms AspisR1.NMO_ArrayStored.blind_written
#check @AspisR1.NMO_ArrayStored.blind_written
#print axioms AspisR1.NMO_ArrayStored.high_preserved
#check @AspisR1.NMO_ArrayStored.high_preserved
#print axioms AspisR1.NMO_ArrayStored.high_written
#check @AspisR1.NMO_ArrayStored.high_written
#print axioms AspisR1.NMO_ArrayStored.low_preserved
#check @AspisR1.NMO_ArrayStored.low_preserved
#print axioms AspisR1.NMO_ArrayStored.low_written
#check @AspisR1.NMO_ArrayStored.low_written
#print axioms AspisR1.NMO_ArrayStored.reachable
#check @AspisR1.NMO_ArrayStored.reachable
#print axioms AspisR1.NMO_ChallengeWindows.complete
#check @AspisR1.NMO_ChallengeWindows.complete
#print axioms AspisR1.NMO_ChallengeWindows.select_zc
#check @AspisR1.NMO_ChallengeWindows.select_zc
#print axioms AspisR1.NMO_ClaimsAtState.alpha
#check @AspisR1.NMO_ClaimsAtState.alpha
#print axioms AspisR1.NMO_ClaimsAtState.claims
#check @AspisR1.NMO_ClaimsAtState.claims
#print axioms AspisR1.NMO_ConstructorMemory.claims_block
#check @AspisR1.NMO_ConstructorMemory.claims_block
#print axioms AspisR1.NMO_ConstructorMemory.frame
#check @AspisR1.NMO_ConstructorMemory.frame
#print axioms AspisR1.NMO_ConstructorMemory.read_populated
#check @AspisR1.NMO_ConstructorMemory.read_populated
#print axioms AspisR1.NMO_ErrorFrontier.terminal_error
#check @AspisR1.NMO_ErrorFrontier.terminal_error
#print axioms AspisR1.NMO_ErrorFrontier.terminal_steps
#check @AspisR1.NMO_ErrorFrontier.terminal_steps
#print axioms AspisR1.NMO_ExtraCell.preserved
#check @AspisR1.NMO_ExtraCell.preserved
#print axioms AspisR1.NMO_ExtraCell.reachable
#check @AspisR1.NMO_ExtraCell.reachable
#print axioms AspisR1.NMO_ExtraCell.written
#check @AspisR1.NMO_ExtraCell.written
#print axioms AspisR1.NMO_ExtraStored.preserved
#check @AspisR1.NMO_ExtraStored.preserved
#print axioms AspisR1.NMO_ExtraStored.reachable
#check @AspisR1.NMO_ExtraStored.reachable
#print axioms AspisR1.NMO_ExtraStored.written
#check @AspisR1.NMO_ExtraStored.written
#print axioms AspisR1.NMO_ExtraValue.decoded
#check @AspisR1.NMO_ExtraValue.decoded
#print axioms AspisR1.NMO_MaskAtState.arguments
#check @AspisR1.NMO_MaskAtState.arguments
#print axioms AspisR1.NMO_MaskStored.preserved
#check @AspisR1.NMO_MaskStored.preserved
#print axioms AspisR1.NMO_MaskStored.reachable
#check @AspisR1.NMO_MaskStored.reachable
#print axioms AspisR1.NMO_MaskStored.written
#check @AspisR1.NMO_MaskStored.written
#print axioms AspisR1.NMO_MaskValue.from_probe
#check @AspisR1.NMO_MaskValue.from_probe
#print axioms AspisR1.NMO_MaskValue.source
#check @AspisR1.NMO_MaskValue.source
#print axioms AspisR1.NMO_MaskValue.to_probe
#check @AspisR1.NMO_MaskValue.to_probe
#print axioms AspisR1.NMO_MulAtState.operands
#check @AspisR1.NMO_MulAtState.operands
#print axioms AspisR1.NMO_MulAtState.product
#check @AspisR1.NMO_MulAtState.product
#print axioms AspisR1.NMO_PrefixBounds.native_windows
#check @AspisR1.NMO_PrefixBounds.native_windows
#print axioms AspisR1.NMO_PrefixBounds.record_lengths
#check @AspisR1.NMO_PrefixBounds.record_lengths
#print axioms AspisR1.NMO_PrefixErrors.claims_error
#check @AspisR1.NMO_PrefixErrors.claims_error
#print axioms AspisR1.NMO_PrefixErrors.rounds_abort
#check @AspisR1.NMO_PrefixErrors.rounds_abort
#print axioms AspisR1.NMO_PrefixErrors.rounds_error
#check @AspisR1.NMO_PrefixErrors.rounds_error
#print axioms AspisR1.NMO_TerminalStored.map_written
#check @AspisR1.NMO_TerminalStored.map_written
#print axioms AspisR1.NMO_TerminalStored.reachable
#check @AspisR1.NMO_TerminalStored.reachable
#print axioms AspisR1.NMO_TerminalStored.reply_preserved
#check @AspisR1.NMO_TerminalStored.reply_preserved
#print axioms AspisR1.NMO_TerminalStored.terminal_written
#check @AspisR1.NMO_TerminalStored.terminal_written
#print axioms AspisR1.NMO_TerminalStored.value_preserved
#check @AspisR1.NMO_TerminalStored.value_preserved
#print axioms AspisR1.NMO_TerminalWindows.alpha_complete
#check @AspisR1.NMO_TerminalWindows.alpha_complete
#print axioms AspisR1.NMO_TerminalWindows.claims_complete
#check @AspisR1.NMO_TerminalWindows.claims_complete
#print axioms AspisR1.NMO_Transcription.full_outcome
#check @AspisR1.NMO_Transcription.full_outcome
#print axioms AspisR1.NMO_Transcription.source
#check @AspisR1.NMO_Transcription.source
