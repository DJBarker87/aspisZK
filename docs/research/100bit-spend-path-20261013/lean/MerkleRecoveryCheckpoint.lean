import R1MerkleTable
import R1MerkleProgram
import R1MerkleRecovery
import R1MerkleLeafRecovery
import R1PartialJointList
import R1ParsedTargetsCollision
import R1D2TableBoundary

/-! Focused axiom checkpoint for the finite Merkle table/walk, program and
recovery lemmas, partial-joint list facts, collision accounting, and D2 table
boundary. This audit adds no source or security conclusion. -/

#print axioms AspisR1.MerkleTable.digestDecidableEq
#print axioms AspisR1.MerkleTable.lookup_mem
#print axioms AspisR1.MerkleTable.lookup_exists
#print axioms AspisR1.MerkleTable.targets_length
#print axioms AspisR1.MerkleTable.root_mem_targets
#print axioms AspisR1.MerkleTable.child_mem_targets
#print axioms AspisR1.MerkleTable.walk_mem_targets

#print axioms AspisR1.MerkleProgram.eval_pathProgram
#print axioms AspisR1.MerkleProgram.eval_leafProgram
#print axioms AspisR1.MerkleProgram.pathProgram_accepts_iff
#print axioms AspisR1.MerkleProgram.leafProgram_accepts_iff

#print axioms AspisR1.MerkleRecovery.walk_reconstruct
#print axioms AspisR1.MerkleRecovery.recover_or_bad

#print axioms AspisR1.MerkleLeafRecovery.lookupLeaf_mem
#print axioms AspisR1.MerkleLeafRecovery.recover_or_bad

#print axioms AspisR1.PartialJointList.exactInitialEncoder_zero
#print axioms AspisR1.PartialJointList.selectedSupport_eq_joint
#print axioms AspisR1.PartialJointList.projected_response_mem_lambda
#print axioms AspisR1.PartialJointList.partial_family_card_le_100

#print axioms AspisR1.ParsedTargetsCollision.density
#print axioms AspisR1.ParsedTargetsCollision.mass

#print axioms AspisR1.D2TableBoundary.table_flip_cost
