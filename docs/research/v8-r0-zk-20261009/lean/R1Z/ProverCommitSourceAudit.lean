import R1Z.ProverCommitGrammarSource
import R1Z.ProverCommitExhaustionScope
import R1Z.PrivacyR1Final
/-! Coherent env J audit of the additive source facts and the unchanged,
conditional privacy endpoint. This does not instantiate its Rust premises. -/
#print axioms R1Z.ProverCommitSaltSource.salt_source
#print axioms R1Z.ProverCommitSaltBytes.shift_byte
#print axioms R1Z.ProverCommitSaltBytes.le32_source
#print axioms R1Z.ProverCommitSaltBytes.le64_source
#print axioms R1Z.ProverCommitSaltBytes.salt_bytes
#print axioms R1Z.ProverCommitLeafSource.leaf_source
#print axioms R1Z.ProverCommitLeafSource.tag_eq
#print axioms R1Z.ProverCommitLeafSource.leaf_shared
#print axioms R1Z.ProverCommitStreamSource.mask_block
#print axioms R1Z.ProverCommitStreamSource.source_block
#print axioms R1Z.ProverCommitStreamSource.mask_seed
#print axioms R1Z.ProverCommitStreamBytes.block_bytes
#print axioms R1Z.ProverCommitStreamBytes.mask_domain
#print axioms R1Z.ProverCommitStreamBytes.source_domain
#print axioms R1Z.ProverCommitStreamBytes.mask_seed_domain
#print axioms R1Z.ProverCommitStreamBytes.counter_step
#print axioms R1Z.ProverCommitStreamBytes.word_byte_index
#print axioms R1Z.ProverCommitGrammarSource.salt_gram
#print axioms R1Z.ProverCommitGrammarSource.mask_gram
#print axioms R1Z.ProverCommitGrammarSource.source_gram
#print axioms R1Z.ProverCommitGrammarSource.leaf_gram
#print axioms R1Z.ProverCommitExhaustionScope.accepted_prefix
#print axioms R1Z.ProverCommitExhaustionScope.rejected_suffix
#print axioms R1Z.ProverCommitExhaustionScope.exhausted_succ
#print axioms R1Z.ProverCommitExhaustionScope.padded_converse_false
#print axioms R1Z.ProverCommitExhaustionScope.worst_budget_counterexample
#print axioms R1Z.PrivacyR1Final.privacy_R1_final
