import LogA_Dependencies
import LogA_PublicBytes
set_option autoImplicit false
/-! Final focused audit only. No transport, manifest replay or source adoption. -/
#print axioms AspisR1.LogA_Tags.prefix_free
#print axioms AspisR1.LogA_Tags.fixed_prefix_injective
#print axioms AspisR1.LogA_Tags.squeeze_advance_separate
#print axioms AspisR1.LogA_Tags.short_absorb_separate
#print axioms AspisR1.LogA_Tags.semantic_domain
#print axioms AspisR1.LogA_Dependencies.verifier_initial_head
#print axioms AspisR1.LogA_Dependencies.query_states_agree
#print axioms AspisR1.LogA_Dependencies.plain_inputs
#print axioms AspisR1.LogA_Dependencies.leaf_first
#print axioms AspisR1.LogA_Dependencies.checksum_input_agree
#print axioms AspisR1.LogA_PublicBytes.physical_ne_semantic
#print axioms AspisR1.LogA_PublicBytes.changed_digest_changes_address
