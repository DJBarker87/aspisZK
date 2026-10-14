import R1CanonicalLogInputs
import R1FixedOffsetTarget
import R1CanonicalPredictedRecovery
import R1CanonicalMerkleCollision
import R1CanonicalBoundRecovery
import R1ParsedTargetsCollision
import R1MerkleChildTargets
import R1CommitmentRootTargets
import R1CommitmentRootFrames
import R1ThreeCommitmentRecovery

/-! Combined public-axiom checkpoint for canonical-log recovery, target
predictors, and the three literal commitment-frame specializations. -/

#print axioms AspisR1.CanonicalLogInputs.mem_input
#print axioms AspisR1.CanonicalLogInputs.input_length_le
#print axioms AspisR1.CanonicalLogInputs.input_read
#print axioms AspisR1.CanonicalLogInputs.encode_ne
#print axioms AspisR1.FixedOffsetTarget.parse
#print axioms AspisR1.FixedOffsetTarget.parse_ofBytes

#print axioms AspisR1.CanonicalPredictedRecovery.recover_or_events
#print axioms AspisR1.CanonicalMerkleCollision.read_witness
#print axioms AspisR1.CanonicalMerkleCollision.hits_collision
#print axioms AspisR1.CanonicalBoundRecovery.recover_or_events
#print axioms AspisR1.CanonicalBoundRecovery.recover_of_no_events

#print axioms AspisR1.ParsedTargetsCollision.density
#print axioms AspisR1.ParsedTargetsCollision.mass
#print axioms AspisR1.MerkleChildTargets.pred_ofBytes
#print axioms AspisR1.MerkleChildTargets.mass
#print axioms AspisR1.CommitmentRootTargets.pred_tail
#print axioms AspisR1.CommitmentRootTargets.pred_middle
#print axioms AspisR1.CommitmentRootTargets.mass

#print axioms AspisR1.CommitmentRootFrames.c2Prefix_length
#print axioms AspisR1.CommitmentRootFrames.c2Frame_length
#print axioms AspisR1.CommitmentRootFrames.foldedPrefix_length
#print axioms AspisR1.CommitmentRootFrames.foldedFrame_length
#print axioms AspisR1.CommitmentRootFrames.pred_c1
#print axioms AspisR1.CommitmentRootFrames.pred_c2
#print axioms AspisR1.CommitmentRootFrames.pred_folded

#print axioms AspisR1.ThreeCommitmentRecovery.c1_recover_of_no_events
#print axioms AspisR1.ThreeCommitmentRecovery.c2_recover_of_no_events
#print axioms AspisR1.ThreeCommitmentRecovery.folded_recover_of_no_events
