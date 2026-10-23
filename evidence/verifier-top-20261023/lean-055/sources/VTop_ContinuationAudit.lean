import VTop_Audit
import VTop_ObservationBoundary
import VTop_OracleStages
import VTop_Annotation
import OraclePortHeadlineFrozen2PerAttempt

/-! Focused compatible-import and standard-axiom audit, not a release replay.
The headline is imported to check compatibility, not to assert its source
execution-join premise has been discharged. -/
#print axioms AspisR1.VTop_ObservationBoundary.extraRead_value
#print axioms AspisR1.VTop_ObservationBoundary.extraRead_observation
#print axioms AspisR1.VTop_ObservationBoundary.reads_value
#print axioms AspisR1.VTop_ObservationBoundary.reads_length
#print axioms AspisR1.VTop_ObservationBoundary.no_unbound_verifier_join
#print axioms AspisR1.VTop_OracleCode.accepted_interpret_eq
#print axioms AspisR1.VTop_OracleStages.all_calls
#print axioms AspisR1.VTop_OracleStages.accepted_tx1
#print axioms AspisR1.VTop_OracleStages.accepted_tx2_common
#print axioms AspisR1.VTop_OracleStages.accepted_tx2_authenticated
#print axioms AspisR1.VTop_Annotation.two_pass
#print AspisR1.VTop_OracleStages.ConeJoins
#print AspisR1.VTop_OracleCode.CallJoin
#print AspisR1.VTop_Annotation.two_pass
#check AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness
