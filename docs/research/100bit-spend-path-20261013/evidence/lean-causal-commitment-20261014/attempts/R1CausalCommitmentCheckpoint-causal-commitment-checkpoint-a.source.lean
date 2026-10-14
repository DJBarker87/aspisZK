import R1C1BeforeFrameStability
import R1LaterCommitmentStability
import R1CombinedMerkleCollision
import R1MerkleIndexGeometry
import R1RecoveredRootRecorded

/-! Focused public-axiom checkpoint for causal recovery at all three
commitments and the common full-trace hash event. This is not an extraction,
Fiat--Shamir, privacy, or Rust correspondence theorem. -/

#print axioms AspisR1.CanonicalRecoveryStability.recover_stable
#print axioms AspisR1.C1BeforeFrameStability.c1_word_stable
#print axioms AspisR1.LaterCommitmentStability.c2_word_stable
#print axioms AspisR1.LaterCommitmentStability.folded_word_stable
#print axioms AspisR1.CombinedMerkleCollision.hits_equiv
#print axioms AspisR1.CombinedMerkleCollision.hitsBad_mono
#print axioms AspisR1.CombinedMerkleCollision.outside
#print axioms AspisR1.CombinedMerkleCollision.old_included
#print axioms AspisR1.CombinedMerkleCollision.mass
#print axioms AspisR1.MerkleIndexGeometry.length_slots
#print axioms AspisR1.MerkleIndexGeometry.index_slots
#print axioms AspisR1.MerkleIndexGeometry.foldedIndex_decompose
#print axioms AspisR1.MerkleIndexGeometry.slots6_injective
#print axioms AspisR1.RecoveredRootRecorded.canonical_root_read
