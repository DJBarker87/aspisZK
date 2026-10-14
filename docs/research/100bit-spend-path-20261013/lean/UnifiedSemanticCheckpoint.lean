import R1UnifiedSemanticCase
import R1UnifiedSemanticLaw

/-! Combined import and axiom audit for the ordinary semantic decoder case.
Run after the focused targets, without replaying unchanged manifests. -/

#print axioms AspisR1.PrefixNextTrace.follows_after_prefix
#print axioms AspisR1.UnifiedSemanticContext.parse_of_checks
#print axioms AspisR1.UnifiedSemanticContext.parse_sound
#print axioms AspisR1.UnifiedSemanticFacts.semantic_records_have_cells_and_squeeze_reads
#print axioms AspisR1.UnifiedSemanticDecoder.decode_of_parse
#print axioms AspisR1.UnifiedSemanticDecoder.decode_sound
#print axioms AspisR1.UnifiedSemanticDecoder.output_round
#print axioms AspisR1.UnifiedSemanticDecoder.decoded_round_bounds
#print axioms AspisR1.UnifiedSemanticDecoder.follows_map
#print axioms AspisR1.UnifiedOrdinaryFirstCell.firstCell_eq
#print axioms AspisR1.UnifiedSemanticLaw.background_sampler_law
#print axioms AspisR1.UnifiedSemanticLaw.decoded_bound
#print axioms AspisR1.UnifiedSemanticActualView.actual_output
#print axioms AspisR1.UnifiedSemanticInjection.decodes_and_follows
#print axioms AspisR1.UnifiedSemanticCase.decodes_and_follows
