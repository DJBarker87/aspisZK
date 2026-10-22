import MultiproofConeFrozen2Stage
import MultiproofConeSlotAdapters
import MultiproofConePhysicalFreeze

/-! Final focused accepted multiproof-stage audit. The endpoint concerns the
explicit instrumented/P6 source cut and the two frozen2 batch programs.
Initial key/stored-carrier equations and S2 Rust caller lowering are excluded.
This module does not construct the global verifier or annotation join. -/
#check AspisR1.MultiproofConeFrozen2Stage.both_batches
#print axioms AspisR1.MultiproofConeLeafContent.step_exact
#print axioms AspisR1.MultiproofConeLeafFrozen.batch_leaves
#print axioms AspisR1.MultiproofConeCountPhysical.rows_projection
#print axioms AspisR1.MultiproofConeCountPhysicalLevels.eighteen_count
#print axioms AspisR1.MultiproofConeCountPhysicalLevels.unread_domain
#print axioms AspisR1.MultiproofConeCountBounds.eighteen_bound
#print axioms AspisR1.MultiproofConePadding.padding
#print axioms AspisR1.MultiproofConeRootGuard.root_guard
#print axioms AspisR1.MultiproofConePhysicalVerify.accepted_verify
#print axioms AspisR1.MultiproofConeSlotTail.slot_count_eq
#print axioms AspisR1.MultiproofConeSlotTail.accepted_tail
#print axioms AspisR1.MultiproofConeSlotState.accepted_slot
#print axioms AspisR1.MultiproofConeBatches.accepted_sequence
#print axioms AspisR1.MultiproofConeFrozen2Stage.both_batches
#print axioms AspisR1.MultiproofConeFrozen2Stage.accepted_outer
#print axioms AspisR1.MultiproofConeSlotAdapters.slot_view
#print axioms AspisR1.OraclePortFrozen2Join.acceptedRunJoin_of_cones
#print axioms AspisR1.OraclePortHeadlineFrozen2PerAttempt.final_soundness
