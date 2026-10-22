import R1Z.ProverCommitCompact43
import R1Z.ProverCommitLeaves43
import R1Z.ProverCommitNative43
import R1Z.ProverCommitPadding43
import R1Z.ProverCommitPublish43
import R1Z.ProverCommitDeployedFuel22

/-! Focused audit of the completed local part-43 proof cone.
No complete native simulator publication, FS conversion or deployed join is claimed. -/

#print axioms R1Z.ProverCommitCompact43.low_length
#print axioms R1Z.ProverCommitCompact43.cell_ok
#print axioms R1Z.ProverCommitCompact43.values_loop
#print axioms R1Z.ProverCommitCompact43.values_ok
#print axioms R1Z.ProverCommitCompact43.values_length
#print axioms R1Z.ProverCommitCompact43.semantic_loop
#print axioms R1Z.ProverCommitLeaves43.fold_decode
#print axioms R1Z.ProverCommitLeaves43.pair_step
#print axioms R1Z.ProverCommitLeaves43.folded_step
#print axioms R1Z.ProverCommitLeaves43.pair_loop
#print axioms R1Z.ProverCommitLeaves43.folded_loop
#print axioms R1Z.ProverCommitLeaves43.ordered_loop
#print axioms R1Z.ProverCommitNative43.run_step
#print axioms R1Z.ProverCommitNative43.increment
#print axioms R1Z.ProverCommitNative43.range_run
#print axioms R1Z.ProverCommitNative43.generate_owner
#print axioms R1Z.ProverCommitNative43.continuation
#print axioms R1Z.ProverCommitPadding43.extend
#print axioms R1Z.ProverCommitPadding43.reject
#print axioms R1Z.ProverCommitPadding43.accepts
#print axioms R1Z.ProverCommitPadding43.model
#print axioms R1Z.ProverCommitPublish43.query_step
#print axioms R1Z.ProverCommitPublish43.query_loop
#print axioms R1Z.ProverCommitPublish43.query_exact
#print axioms R1Z.ProverCommitPublish43.slot_length
#print axioms R1Z.ProverCommitPublish43.slots_loop
#print axioms R1Z.ProverCommitPublish43.slots_length
#print axioms R1Z.ProverCommitPublish43.assemble_loop
#print axioms R1Z.ProverCommitPublish43.proof_error
#print axioms R1Z.ProverCommitPublish43.replay_error
#print axioms R1Z.ProverCommitPublish43.replay_disagreement
#print axioms R1Z.ProverCommitPublish43.merkle_collision
#print axioms R1Z.ProverCommitPublish43.merge_error
#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed
