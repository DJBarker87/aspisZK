import R1Z.RealR1_OuterOwner
import R1Z.RealR1_ReachableRetry
import R1Z.RealR1_RetryHazards

/-! One final focused import/axioms audit; no frozen manifest or release claim.
The statements printed here expose all retained contracts for lead review. -/
#print R1Z.RealR1_OuterOwner.BodyContract
#print R1Z.RealR1_OuterOwner.PrefixContract
#print R1Z.RealR1_OuterOwner.outer_owner
#print R1Z.RealR1_ReachableRetry.Ready
#print R1Z.RealR1_ReachableRetry.PreparedBodyContract
#print R1Z.RealR1_ReachableRetry.outer_owner_reachable
#print R1Z.RealR1_RetryHazards.selected_trace
#print R1Z.RealR1_RetryHazards.entered_abort_hazard
#print axioms R1Z.RealR1_OuterOwner.entropy_exact
#print axioms R1Z.RealR1_OuterOwner.reserved_exact
#print axioms R1Z.RealR1_OuterOwner.outer_owner
#print axioms R1Z.RealR1_OuterOwner.wrong_variant
#print axioms R1Z.RealR1_OuterOwner.entropy_failure_stops
#print axioms R1Z.RealR1_OuterOwner.reservation_failure_closed
#print axioms R1Z.RealR1_OuterOwner.duplicate_closed
#print axioms R1Z.RealR1_ReachableRetry.prepared_attempt
#print axioms R1Z.RealR1_ReachableRetry.run_reachable
#print axioms R1Z.RealR1_ReachableRetry.outer_owner_reachable
#print axioms R1Z.RealR1_RetryHazards.selected_trace
#print axioms R1Z.RealR1_RetryHazards.entered_abort_hazard
#print axioms R1Z.RealR1_RetryHazards.entropy_count_state
