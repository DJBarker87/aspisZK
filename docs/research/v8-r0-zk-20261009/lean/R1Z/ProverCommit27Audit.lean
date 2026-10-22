import R1Z.ProverCommitCoinTape27
import R1Z.ProverCommitCursorMarginal27
import R1Z.ProverCommitTranscriptTape27
import R1Z.ProverCommitExtractedCoin27
import R1Z.ProverCommitCoinCall27
import R1Z.ProverCommitCoinSequence27
import R1Z.ProverCommitMachineMarginal27
import R1Z.ProverCommitEffectCallers27
import R1Z.ProverCommitDeployedFuel22
/-! Coherent changed-cone audit. Does not assert concrete whole-run joins. -/
#print axioms R1Z.ProverCommitCoinTape27.call_preserves
#print axioms R1Z.ProverCommitCoinTape27.sequence_preserves
#print axioms R1Z.ProverCommitCoinTape27.cursor_history
#print axioms R1Z.ProverCommitCursorMarginal27.source_execution
#print axioms R1Z.ProverCommitCursorMarginal27.native_source_execution
#print axioms R1Z.ProverCommitCursorMarginal27.model_execution
#print axioms R1Z.ProverCommitTranscriptTape27.stream_disjoint
#print axioms R1Z.ProverCommitTranscriptTape27.transcript_unchanged
#print axioms R1Z.ProverCommitTranscriptTape27.product_coins
#print axioms R1Z.ProverCommitTranscriptTape27.execution_law
#print axioms R1Z.ProverCommitExtractedCoin27.bytes_ext
#print axioms R1Z.ProverCommitExtractedCoin27.bytes_eq_iff
#print axioms R1Z.ProverCommitExtractedCoin27.byte_bne
#print axioms R1Z.ProverCommitExtractedCoin27.different0_eq
#print axioms R1Z.ProverCommitExtractedCoin27.different8_eq
#print axioms R1Z.ProverCommitExtractedCoin27.different16_eq
#print axioms R1Z.ProverCommitExtractedCoin27.different24_eq
#print axioms R1Z.ProverCommitExtractedCoin27.or_result
#print axioms R1Z.ProverCommitExtractedCoin27.different_eq
#print axioms R1Z.ProverCommitCoinCall27.read_total
#print axioms R1Z.ProverCommitCoinCall27.call_exact
#print axioms R1Z.ProverCommitCoinSequence27.generated_sequence
#print axioms R1Z.ProverCommitCoinSequence27.step_view
#print axioms R1Z.ProverCommitMachineMarginal27.initial_product
#print axioms R1Z.ProverCommitMachineMarginal27.generated_source_law
#print axioms R1Z.ProverCommitMachineMarginal27.generated_model_law
#print axioms R1Z.ProverCommitEffectCallers27.semantic_call
#print axioms R1Z.ProverCommitEffectCallers27.block_call
#print axioms R1Z.ProverCommitEffectCallers27.dictionary_exact
#print axioms R1Z.ProverCommitEffectCallers27.query_effects
#print axioms R1Z.ProverCommitEffectCallers27.semantic_history_length
#print axioms R1Z.ProverCommitEffectCallers27.block_history_length
#print axioms R1Z.PrivacyR1HeadlineDeployed.privacy_headline_deployed
#print axioms R1Z.ProverCommitDeployedFuel22.privacy_headline_deployed
#check AspisR1CoinEffect27.EffectDigest32
#check AspisR1EffectCallers27.Digest32
#check AspisR1SimControl21.aspis_core.digest.Digest32
#check R1Z.ProverCommitCoinSequence27.evaluate
#check R0Z.FsStatement.FSExperiments
