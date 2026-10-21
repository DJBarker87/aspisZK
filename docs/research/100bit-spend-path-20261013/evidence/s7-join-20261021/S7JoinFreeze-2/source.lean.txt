import S7JoinGeometryGroups
import S7JoinBasisCanonical
import S7JoinBackendCarriers
import S7JoinFrozenConsumer
import S7JoinAccumulation

/-! Compatible focused union of the S7 accepted-consumer continuation.
This is not the complete frozen source dependency/release manifest. -/
#print axioms AspisR1.S7JoinGeometryGroups.inversion_groups
#print axioms AspisR1.S7JoinBasisCanonical.total_exact
#print axioms AspisR1.S7JoinBackendCarriers.multiply_exact
#print axioms AspisR1.S7JoinBackendCarriers.canonicalize_exact
#print axioms AspisR1.S7JoinFrozenConsumer.decision_eq
#print axioms AspisR1.S7JoinFrozenConsumer.accepted_matching_query

#print axioms AspisR1.S7JoinRowsTrace.rows_exact
#print axioms AspisR1.S7JoinQueryRows.query_rows_exact
#print axioms AspisR1.S7JoinAccumulation.total_exact
