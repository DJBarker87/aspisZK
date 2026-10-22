import R1Z.ProverCommitConditionalRom41
import R1Z.ProverCommitPublicPrefix41
import R1Z.ProverCommitMixedReads41
import R1Z.ProverCommitPublicCoins41
import R1Z.ProverCommitBindingErase41
import R1Z.ProverCommitDeployedFuel22

/-! Focused audit only. The conditional read laws do not instantiate either
concrete WholeRunJoin or discharge RustProverRefinement. -/
#print axioms R1Z.ProverCommitConditionalRom41.conditional_law
#print axioms R1Z.ProverCommitConditionalRom41.history_fiber
#print axioms R1Z.ProverCommitConditionalRom41.programmed_history
#print axioms R1Z.ProverCommitPublicPrefix41.reads_preserved
#print axioms R1Z.ProverCommitPublicPrefix41.reads_of_slice
#print axioms R1Z.ProverCommitPublicPrefix41.grammar_binding1
#print axioms R1Z.ProverCommitPublicPrefix41.lookup_frozen
#print axioms R1Z.ProverCommitPublicPrefix41.context_local
#print axioms R1Z.ProverCommitPublicPrefix41.conditional_public_prefix
#print axioms R1Z.ProverCommitPublicPrefix41.raw_off_history
#print axioms R1Z.ProverCommitMixedReads41.coherent_answers
#print axioms R1Z.ProverCommitMixedReads41.run_eq_mixed
#print axioms R1Z.ProverCommitMixedReads41.first_memo
#print axioms R1Z.ProverCommitPublicCoins41.addresses_causal
#print axioms R1Z.ProverCommitPublicCoins41.conditional_law
#print axioms R1Z.ProverCommitPublicCoins41.run_eq
#print axioms R1Z.ProverCommitBindingErase41.rebind_child
#print axioms R1Z.ProverCommitBindingErase41.opened_address
#print axioms R1Z.ProverCommitBindingErase41.opened_answer
#print axioms R1Z.ProverCommitBindingErase41.opened_log
#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed
