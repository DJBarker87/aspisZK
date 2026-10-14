import R1UnifiedPayloadZero
import R1UnifiedCanonicalProver
import R1UnifiedDecoder
import R1UnifiedDispatchAddress
import R1UnifiedDispatchCase
import R1UnifiedDecoderBound
import R1UnifiedChainDensity
import R1UnifiedTotalCase
import R1UnifiedInj
import R1UnifiedFiatShamir

/-! One combined import and axiom audit after the focused unified FS targets pass.
This checkpoint retains the final theorem's explicit D1/D2/D3 conditions. -/

#print axioms AspisR1.UnifiedPayloadZero.payload_zero
#print axioms AspisR1.UnifiedPayloadZero.payload_ne_zero
#print axioms AspisR1.UnifiedPayloadZero.message_eq
#print axioms AspisR1.UnifiedPayloadZero.transcript_eq
#print axioms AspisR1.UnifiedPayloadZero.challenge_eq
#print axioms AspisR1.UnifiedPayloadZero.state_eq
#print axioms AspisR1.UnifiedPayloadZero.protocol_message_eq
#print axioms AspisR1.UnifiedPayloadZero.protocol_transcript_eq
#print axioms AspisR1.UnifiedPayloadZero.protocol_chain_eq
#print axioms AspisR1.UnifiedPayloadZero.protocol_challenge_eq
#print axioms AspisR1.UnifiedPayloadZero.verifier_eq
#print axioms AspisR1.UnifiedCanonicalProver.eval_prover
#print axioms AspisR1.UnifiedCanonicalProver.codec
#print axioms AspisR1.UnifiedCanonicalProver.experiment_trace_eq
#print axioms AspisR1.UnifiedDecoder.component_initial
#print axioms AspisR1.UnifiedDecoder.component_semantic
#print axioms AspisR1.UnifiedDecoder.component_reseed
#print axioms AspisR1.UnifiedDecoder.component_opening
#print axioms AspisR1.UnifiedDecoder.component_query
#print axioms AspisR1.UnifiedDecoder.component_rho
#print axioms AspisR1.UnifiedDecoder.component_none
#print axioms AspisR1.UnifiedDecoder.decode_of_init_parse
#print axioms AspisR1.UnifiedDecoder.decode_of_absorb
#print axioms AspisR1.UnifiedDecoder.decode_sound
#print axioms AspisR1.UnifiedDispatchAddress.firstCell_nonzero
#print axioms AspisR1.UnifiedDispatchAddress.decode_at_first
#print axioms AspisR1.UnifiedDispatchCase.decodes_and_follows
#print axioms AspisR1.UnifiedDecoderBound.component_bound
#print axioms AspisR1.UnifiedDecoderBound.decoded_bound
#print axioms AspisR1.UnifiedChainDensity.chainDensity
#print axioms AspisR1.UnifiedTotalCase.decodes_and_follows
#print axioms AspisR1.UnifiedInj.inj
#print axioms AspisR1.UnifiedFiatShamir.soundness_bound
