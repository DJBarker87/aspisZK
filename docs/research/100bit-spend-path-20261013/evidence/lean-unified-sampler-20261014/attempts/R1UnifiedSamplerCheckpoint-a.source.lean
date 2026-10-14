import R1UnifiedContinuation
import R1UnifiedSamplerLaw

/-! Focused sampler/continuation checkpoint. This does not instantiate the
full Fiat--Shamir theorem or the source and privacy obligations. -/
#print axioms AspisR1.QuerySampler.state_succ'
#print axioms AspisR1.QuerySampler.chain_out
#print axioms AspisR1.QuerySampler.chain_reads
#print axioms AspisR1.QuerySamplerBridge.output
#print axioms AspisR1.QuerySamplerBridge.reads_absorb
#print axioms AspisR1.QuerySamplerBridge.reads_pairs
#print axioms AspisR1.RowZeroCodec.row0_absorb
#print axioms AspisR1.RowZeroCodec.decoded_empty
#print axioms AspisR1.RowZeroCodec.indexed_empty
#print axioms AspisR1.DuplexSamplers.plain_eval
#print axioms AspisR1.DuplexSamplers.initial_eval
#print axioms AspisR1.DuplexSamplers.reseeded_eval
#print axioms AspisR1.DuplexSamplers.plain_own_matches
#print axioms AspisR1.DuplexSamplers.initial_own_matches
#print axioms AspisR1.DuplexSamplers.reseeded_own_matches
#print axioms AspisR1.UnifiedSampler.row_zero
#print axioms AspisR1.UnifiedSampler.row_reseed
#print axioms AspisR1.UnifiedSampler.row_query
#print axioms AspisR1.UnifiedSampler.row_rho
#print axioms AspisR1.UnifiedSampler.firstCell_some
#print axioms AspisR1.UnifiedSampler.unified_law
#print axioms AspisR1.UnifiedContinuation.absorb_ext
#print axioms AspisR1.UnifiedContinuation.query_then_rho_state
#print axioms AspisR1.UnifiedContinuation.query_then_rho_firstCell
