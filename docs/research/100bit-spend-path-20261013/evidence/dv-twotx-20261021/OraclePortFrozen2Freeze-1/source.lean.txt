import OraclePortHeadlineFrozen2PerAttempt
import OraclePortFrozen2Cones
import OraclePortFrozen2Equivalence
import OraclePortFrozen2Digests
import OraclePortFrozen2RoundTripLog
import Frozen2StartChargeCheckpoint

/-! One final focused union and standard-axioms audit. Historical dependencies
are reused from pinned caches; this is not a full frozen release replay. -/
#print axioms AspisR1.OraclePortFrozen2.acceptance_eq
#print axioms AspisR1.OraclePortFrozen2.verifier_acceptance_eq
#print axioms AspisR1.OraclePortFrozen2.annotated_acceptance_eq
#print axioms AspisR1.OraclePortFrozen2.roundtrip_log
#print axioms AspisR1.OraclePortFrozen2.six_inserted
#print axioms AspisR1.OraclePortFrozen2.annotated_twelve_inserted
#print axioms AspisR1.OraclePortFrozen2Digests.six_ordered_reads
#print axioms AspisR1.OraclePortFrozen2.decision_budget
#print axioms AspisR1.OraclePortFrozen2.verifier_bound
#print axioms AspisR1.OraclePortFrozen2.log_length
#print axioms AspisR1.OraclePortFrozen2ActualChecks.accepted_checks
#print axioms AspisR1.OraclePortFrozen2C6.checked_acceptance
#print axioms AspisR1.OraclePortFrozen2Join.acceptedRunJoin_of_total_cones
#print axioms AspisR1.Frozen2StartChargePrefix.starts
#print axioms AspisR1.Frozen2StartChargeCheckpoint.no_new_start
#print axioms AspisR1.Frozen2StartChargeProbability.failure_bound
#print axioms AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness
#print axioms AspisR1.OraclePortHeadlineFrozen2PerAttempt.failure_bound
#print axioms AspisR1.OraclePortHeadlineFrozen2PerAttempt.zero_queries
