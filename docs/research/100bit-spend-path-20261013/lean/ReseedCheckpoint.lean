import R1ReseedRound
import R1QueryTraceCheckpoint

/-! Combined focused import and axioms audit. This is not the full R1
Fiat--Shamir, Rust correspondence, or privacy theorem. -/
#print axioms AspisR1.ParsedStateCollision.density
#print axioms AspisR1.ParsedStateCollision.mass
#print axioms AspisR1.ParsedStateTrace.no_parsed_before
#print axioms AspisR1.ParsedStateTrace.parsed_after
#print axioms AspisR1.ParsedStateTrace.mass
#print axioms AspisR1.TrailingStateFrame.frame_injective
#print axioms AspisR1.TrailingStateFrame.frame_drop_prefix
#print axioms AspisR1.TrailingStateFrame.tailState_frameAddr
#print axioms AspisR1.OpeningReseedFrame.frame_length
#print axioms AspisR1.OpeningReseedFrame.addr_bytes
#print axioms AspisR1.OpeningReseedFrame.tailState_addr
#print axioms AspisR1.OpeningReseedFrame.addr_length
#print axioms AspisR1.OpeningReseedFrame.frame_binding
#print axioms AspisR1.ReseedBoundary.findCell_correct
#print axioms AspisR1.ReseedBoundary.recover_before_next
#print axioms AspisR1.ReseedSamplerLaw.own_law
#print axioms AspisR1.ReseedSamplerLaw.background_law
#print axioms AspisR1.ReseedTrace.follows
#print axioms AspisR1.ReseedRound.firstCell_sampler
#print axioms AspisR1.ReseedRound.sampler_eval
#print axioms AspisR1.ReseedRound.sampler_law
#print axioms AspisR1.ReseedRound.own_matches_sampler
#print axioms AspisR1.ReseedRound.same_challenge_law
#print axioms AspisR1.QueryNextDecoder.decodes_after_query
#print axioms AspisR1.QueryRhoAcceptance.continuation_accepted_miss_lt_two_neg_119
