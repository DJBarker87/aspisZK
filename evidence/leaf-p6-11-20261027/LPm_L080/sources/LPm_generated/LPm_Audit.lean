import LPm_BytePorts
import LPm_CheckpointBody
import LPm_CheckpointDomains
import LPm_CheckpointLeaf
import LPm_CheckpointProgram
import LPm_CheckpointTrace
import LPm_CheckpointWitness
import LPm_DotPort
import LPm_FieldCarriers
import LPm_FinishPort
import LPm_PointLength
import LPm_PointLoop
import LPm_PowersBridge
import LPm_PublicFold
import LPm_PublicPort
import LPm_PublicState
import LPm_PublicTwentyNine
import LPm_RawPort
import LPm_SemanticSelections
import LPm_SixPoints
import LPm_StubBounds
import LPm_UpdatePort
import LPm_WeightLoop
import LPm_WeightedField
import LPm_WordFold
set_option autoImplicit false
-- One final axioms audit of the accepted LPm theorem roots.
#print axioms AspisR1.LPm_BytePorts.e_layout
#print axioms AspisR1.LPm_BytePorts.e_source
#print axioms AspisR1.LPm_CheckpointBody.source_body
#print axioms AspisR1.LPm_CheckpointBody.weights_port
#print axioms AspisR1.LPm_CheckpointDomains.body_length
#print axioms AspisR1.LPm_CheckpointDomains.prefix_length
#print axioms AspisR1.LPm_CheckpointDomains.reached_weight_prefix
#print axioms AspisR1.LPm_CheckpointDomains.q_loop_domain
#print axioms AspisR1.LPm_CheckpointDomains.e_prefix_domain
#print axioms AspisR1.LPm_CheckpointDomains.query_prefix_domain
#print axioms AspisR1.LPm_CheckpointLeaf.native_result
#print axioms AspisR1.LPm_CheckpointProgram.materialize_eq
#print axioms AspisR1.LPm_CheckpointProgram.returned_eq
#print axioms AspisR1.LPm_CheckpointProgram.program_eq
#print axioms AspisR1.LPm_CheckpointProgram.result_and_effects
#print axioms AspisR1.LPm_CheckpointTrace.append_result
#print axioms AspisR1.LPm_CheckpointTrace.body_split
#print axioms AspisR1.LPm_CheckpointTrace.body_bytes
#print axioms AspisR1.LPm_CheckpointTrace.native_result
#print axioms AspisR1.LPm_CheckpointWitness.append_trace
#print axioms AspisR1.LPm_CheckpointWitness.all_replies
#print axioms AspisR1.LPm_DotPort.private_call
#print axioms AspisR1.LPm_FieldCarriers.indexed_values
#print axioms AspisR1.LPm_FieldCarriers.q_values_injective
#print axioms AspisR1.LPm_FieldCarriers.semantic_values
#print axioms AspisR1.LPm_FieldCarriers.coordinate_values
#print axioms AspisR1.LPm_FinishPort.words_injective
#print axioms AspisR1.LPm_FinishPort.from_finish_words
#print axioms AspisR1.LPm_FinishPort.word_eq
#print axioms AspisR1.LPm_FinishPort.source
#print axioms AspisR1.LPm_PointLength.length
#print axioms AspisR1.LPm_PointLength.all_six
#print axioms AspisR1.LPm_PointLoop.model_push
#print axioms AspisR1.LPm_PointLoop.source
#print axioms AspisR1.LPm_PowersBridge.values_injective
#print axioms AspisR1.LPm_PowersBridge.trace_values
#print axioms AspisR1.LPm_PowersBridge.native_result
#print axioms AspisR1.LPm_PublicFold.dot_bound
#print axioms AspisR1.LPm_PublicFold.below46
#print axioms AspisR1.LPm_PublicFold.step
#print axioms AspisR1.LPm_PublicFold.trace_value
#print axioms AspisR1.LPm_PublicPort.raw_values_injective
#print axioms AspisR1.LPm_PublicPort.raw_meaning
#print axioms AspisR1.LPm_PublicPort.state_ext
#print axioms AspisR1.LPm_PublicPort.source
#print axioms AspisR1.LPm_PublicState.private_source
#print axioms AspisR1.LPm_PublicState.source
#print axioms AspisR1.LPm_PublicTwentyNine.source_new
#print axioms AspisR1.LPm_PublicTwentyNine.initial_bound
#print axioms AspisR1.LPm_PublicTwentyNine.source
#print axioms AspisR1.LPm_RawPort.raw_eq
#print axioms AspisR1.LPm_RawPort.state_fields
#print axioms AspisR1.LPm_SemanticSelections.claims
#print axioms AspisR1.LPm_SemanticSelections.extra
#print axioms AspisR1.LPm_SemanticSelections.before_z1
#print axioms AspisR1.LPm_SixPoints.erase
#print axioms AspisR1.LPm_SixPoints.all_six
#print axioms AspisR1.LPm_StubBounds.product
#print axioms AspisR1.LPm_StubBounds.canonical_sum
#print axioms AspisR1.LPm_StubBounds.residue
#print axioms AspisR1.LPm_UpdatePort.word
#print axioms AspisR1.LPm_UpdatePort.sums
#print axioms AspisR1.LPm_WeightLoop.result
#print axioms AspisR1.LPm_WeightLoop.exists_trace
#print axioms AspisR1.LPm_WeightLoop.native_weights
#print axioms AspisR1.LPm_WeightLoop.reached_size
#print axioms AspisR1.LPm_WeightLoop.reached_domain
#print axioms AspisR1.LPm_WeightedField.add
#print axioms AspisR1.LPm_WeightedField.step
#print axioms AspisR1.LPm_WeightedField.trace_value
#print axioms AspisR1.LPm_WordFold.bounded
#print axioms AspisR1.LPm_WordFold.residues
#print axioms AspisR1.LPm_WordFold.twenty_nine
