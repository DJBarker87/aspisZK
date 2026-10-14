import R1CanonicalReadCollision
import R1CanonicalFullTraceRecovery
import R1ThreeCommitmentFullTrace
import R1CombinedMerkleTargets

/-! Combined public-axiom checkpoint for arbitrary-trace Merkle recovery and
its C1, C2, and folded-root specializations. -/

#print axioms AspisR1.CanonicalReadCollision.hits_collision
#print axioms AspisR1.CanonicalFullTraceRecovery.recover_or_events
#print axioms AspisR1.CanonicalFullTraceRecovery.recover_of_no_events
#print axioms AspisR1.ThreeCommitmentFullTrace.c1_recover_of_no_events
#print axioms AspisR1.ThreeCommitmentFullTrace.c2_recover_of_no_events
#print axioms AspisR1.ThreeCommitmentFullTrace.folded_recover_of_no_events
#print axioms AspisR1.CombinedMerkleTargets.pred_child
#print axioms AspisR1.CombinedMerkleTargets.pred_root
#print axioms AspisR1.CombinedMerkleTargets.bad_equiv
#print axioms AspisR1.CombinedMerkleTargets.mass
