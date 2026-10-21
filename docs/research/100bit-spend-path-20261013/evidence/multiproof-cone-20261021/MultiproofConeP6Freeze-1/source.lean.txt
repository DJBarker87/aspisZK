import MultiproofConeP6Frozen2Stage
import MultiproofConeBatchFreeze

/-! Focused compatible-cache closure audit, not a full frozen release replay.
All source/library P6 and S2/S10 caller boundaries remain explicit. -/
#print AspisR1.MultiproofConeP6Frozen2Stage.P6Boundary
#check AspisR1.MultiproofConeP6Verify.verify_in_place_owned
#check AspisR1.MultiproofConeP6Batch.batch_tree_owned
#check AspisR1.MultiproofConeP6Frozen2Stage.function_certificates
#check AspisR1.MultiproofConeP6Frozen2Stage.both_batches
#print axioms AspisR1.MultiproofConeP6Composition.rows_eq
#print axioms AspisR1.MultiproofConeP6Composition.levels_eq
#print axioms AspisR1.MultiproofConeP6Composition.eighteen_owned
#print axioms AspisR1.MultiproofConeP6Verify.verify_in_place_owned
#print axioms AspisR1.MultiproofConeP6Verify.verifyState_eq
#print axioms AspisR1.MultiproofConeP6Batch.leaves_eq
#print axioms AspisR1.MultiproofConeP6Batch.batch_tree_owned
#print axioms AspisR1.MultiproofConeP6Callbacks.three_parents
#print axioms AspisR1.MultiproofConeP6Callbacks.node_gate
#print axioms AspisR1.MultiproofConeP6Frozen2Stage.function_certificates
#print axioms AspisR1.MultiproofConeP6Frozen2Stage.both_batches
#print axioms AspisR1.MultiproofConeFrozen2Stage.accepted_outer
#print axioms AspisR1.MultiproofConeSlotAdapters.slot_view
#print axioms AspisR1.OraclePortFrozen2Join.acceptedRunJoin_of_cones
#print axioms AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness
