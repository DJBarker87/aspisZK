import PV_L2D_CoinAddresses
import PV_L2D_CoinTrace
import PV_L2D_Coins
import PV_L2D_CollectedTrace
import PV_L2D_DivisionBounds
import PV_L2D_ExpanderControls
import PV_L2D_ExpanderPort
import PV_L2D_ExpanderTrace
import PV_L2D_FourLimbs
import PV_L2D_Read4
import PV_L2D_ScalarPort
import PV_L2D_ScalarRender
import PV_L2D_TraceMass
set_option autoImplicit false
/- Scoped helper audit only; no endpoint row premise is discharged. -/
#print axioms PV_L2D_CoinAddresses.same_counter_iff
#print axioms PV_L2D_CoinAddresses.first_cycle_unique
#print axioms PV_L2D_CoinAddresses.repeats
#print axioms PV_L2D_CoinAddresses.native_cycle
#print axioms PV_L2D_CoinAddresses.frame_unique
#print axioms PV_L2D_CoinAddresses.stream_separated
#print axioms PV_L2D_CoinTrace.progress
#print axioms PV_L2D_CoinTrace.some_progress
#print axioms PV_L2D_CoinTrace.none_consumes
#print axioms PV_L2D_CoinTrace.complete_trace
#print axioms PV_L2D_CoinTrace.same_receipt
#print axioms PV_L2D_Coins.seed_fixed
#print axioms PV_L2D_Coins.consumed_le
#print axioms PV_L2D_Coins.counter_exact
#print axioms PV_L2D_Coins.complete_prefix
#print axioms PV_L2D_Coins.zero_continues
#print axioms PV_L2D_Coins.nonzero_terminates
#print axioms PV_L2D_CollectedTrace.after_clock
#print axioms PV_L2D_CollectedTrace.sample_after_clock
#print axioms PV_L2D_CollectedTrace.complete_trace
#print axioms PV_L2D_CollectedTrace.same_counts
#print axioms PV_L2D_DivisionBounds.dividend_bound
#print axioms PV_L2D_DivisionBounds.u64_safe
#print axioms PV_L2D_DivisionBounds.quotient_word
#print axioms PV_L2D_DivisionBounds.remainder_field
#print axioms PV_L2D_DivisionBounds.step_total
#print axioms PV_L2D_DivisionBounds.pass_length
#print axioms PV_L2D_DivisionBounds.pass_bounds
#print axioms PV_L2D_DivisionBounds.step_reconstruct
#print axioms PV_L2D_ExpanderControls.zero_accepts
#print axioms PV_L2D_ExpanderControls.zero_after
#print axioms PV_L2D_ExpanderControls.zero_four
#print axioms PV_L2D_ExpanderControls.initial_nonvacuity
#print axioms PV_L2D_ExpanderPort.seed_unchanged
#print axioms PV_L2D_ExpanderPort.cursor_exact
#print axioms PV_L2D_ExpanderPort.cursor_admitted
#print axioms PV_L2D_ExpanderPort.counter_exact
#print axioms PV_L2D_ExpanderPort.loads_in_bounds
#print axioms PV_L2D_ExpanderPort.trace_public
#print axioms PV_L2D_ExpanderPort.initial_cursor
#print axioms PV_L2D_ExpanderPort.first_refill
#print axioms PV_L2D_ExpanderTrace.next_clock
#print axioms PV_L2D_ExpanderTrace.next_trace
#print axioms PV_L2D_ExpanderTrace.scalar_trace
#print axioms PV_L2D_ExpanderTrace.initial_clock
#print axioms PV_L2D_FourLimbs.complete_four
#print axioms PV_L2D_FourLimbs.consumed_bound
#print axioms PV_L2D_FourLimbs.counts_bound
#print axioms PV_L2D_FourLimbs.success_length
#print axioms PV_L2D_FourLimbs.four_bound
#print axioms PV_L2D_Read4.slice_length
#print axioms PV_L2D_Read4.conversion_bytes
#print axioms PV_L2D_Read4.decode_same
#print axioms PV_L2D_Read4.last_word_offsets
#print axioms PV_L2D_ScalarPort.complete_source
#print axioms PV_L2D_ScalarPort.consumed_bound
#print axioms PV_L2D_ScalarPort.after_exact
#print axioms PV_L2D_ScalarPort.failure_keeps_trace
#print axioms PV_L2D_ScalarPort.stream_length
#print axioms PV_L2D_ScalarRender.positive_when_running
#print axioms PV_L2D_ScalarRender.some_positive
#print axioms PV_L2D_ScalarRender.trace_render
#print axioms PV_L2D_ScalarRender.same_count_trace
#print axioms PV_L2D_TraceMass.translate_at_count
#print axioms PV_L2D_TraceMass.translated_capped
#print axioms PV_L2D_TraceMass.geom_sum
#print axioms PV_L2D_TraceMass.count_value_normalized
#print axioms PV_L2D_TraceMass.complete_mass
