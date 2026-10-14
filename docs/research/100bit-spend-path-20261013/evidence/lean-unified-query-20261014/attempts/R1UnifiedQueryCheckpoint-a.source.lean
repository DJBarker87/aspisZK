import R1BackgroundOwnMap
import R1QueryBackgroundChain
import R1QueryBackgroundLaw
import R1QueryChainTraceFacts
import R1PrefixQueryTrace
import R1UnifiedQueryDecoder
import R1UnifiedQueryLaw
import R1UnifiedQueryView
import R1UnifiedQueryInjection
import R1UnifiedQueryCase
import R1DecoderStateList
import R1UnifiedLabels
import R1PublicInitAbsorbSeparation

/-! One combined import and axiom audit after the focused query targets pass. -/

#print axioms AspisR1.BackgroundOwnMap.map
#print axioms AspisR1.BackgroundOwnMap.pushSpawns_map
#print axioms AspisR1.BackgroundOwnMap.finished_map
#print axioms AspisR1.BackgroundOwnMap.ownCell_map
#print axioms AspisR1.BackgroundOwnMap.stepAsk_map
#print axioms AspisR1.BackgroundOwnMap.bfollow_map
#print axioms AspisR1.BackgroundOwnMap.blaw_map
#print axioms AspisR1.QueryBackgroundChain.evs_chainBS_mem
#print axioms AspisR1.QueryBackgroundChain.runOut_chainBS
#print axioms AspisR1.QueryBackgroundChain.order_chain
#print axioms AspisR1.QueryBackgroundChain.chain_nodup
#print axioms AspisR1.QueryBackgroundLaw.blaw_chainBS
#print axioms AspisR1.QueryBackgroundLaw.independent_chain_law
#print axioms AspisR1.QueryChainTraceFacts.root_before
#print axioms AspisR1.QueryChainTraceFacts.advance_before
#print axioms AspisR1.QueryChainTraceFacts.states_ne
#print axioms AspisR1.QueryChainTraceFacts.known_ne_state
#print axioms AspisR1.PrefixQueryTrace.follows_after_prefix
#print axioms AspisR1.UnifiedQueryDecoder.output_append
#print axioms AspisR1.UnifiedQueryDecoder.output_round
#print axioms AspisR1.UnifiedQueryDecoder.decode_of_parse
#print axioms AspisR1.UnifiedQueryDecoder.decode_sound
#print axioms AspisR1.UnifiedQueryDecoder.decoded_round_eq_31
#print axioms AspisR1.UnifiedQueryLaw.background_sampler_law
#print axioms AspisR1.UnifiedQueryLaw.decoded_bound
#print axioms AspisR1.UnifiedQueryView.actual_output
#print axioms AspisR1.UnifiedQueryView.firstCell_eq
#print axioms AspisR1.UnifiedQueryInjection.decodes_and_follows
#print axioms AspisR1.UnifiedQueryCase.decodes_and_follows
#print axioms AspisR1.DecoderStateList.lift_of_decode
#print axioms AspisR1.DecoderStateList.lift_sound
#print axioms AspisR1.DecoderStateList.lifted_follow
#print axioms AspisR1.DecoderStateList.lifted_law
#print axioms AspisR1.UnifiedLabels.label_val
#print axioms AspisR1.UnifiedLabels.label_zero
#print axioms AspisR1.UnifiedLabels.label_injective
#print axioms AspisR1.UnifiedLabels.row_label
#print axioms AspisR1.PublicInitAbsorbSeparation.parseAbsorb_none_of_init
#print axioms AspisR1.PublicInitAbsorbSeparation.parse_init_absorb_none
