import F3T_AcceptedFacts
import F3T_AcceptedParser
import F3T_AcceptedReplacement
import F3T_AcceptedTransport
import F3T_AccountCharge
import F3T_AccountSource
import F3T_Accounting
import F3T_ActualChecks
import F3T_Admission
import F3T_AlignedRows
import F3T_Bounds
import F3T_ByteCarrier
import F3T_ByteTag
import F3T_ByteTransport
import F3T_Canon
import F3T_CanonicalChecks
import F3T_CanonicalJoin
import F3T_Carried
import F3T_Causal
import F3T_Charged
import F3T_Checked
import F3T_CheckedView
import F3T_Clean
import F3T_Combined
import F3T_Completion
import F3T_Conditional
import F3T_ConditionalClaims
import F3T_ConditionalSum
import F3T_Cost
import F3T_Decision
import F3T_Experiment
import F3T_Frame
import F3T_HeadCanonical
import F3T_InitFrame
import F3T_InitHead
import F3T_InitialConstructor
import F3T_InputAgreement
import F3T_Installed
import F3T_InstalledRecovered
import F3T_JoinBoundary
import F3T_Leaves
import F3T_ModelClaims
import F3T_Numeric
import F3T_ParsedRows
import F3T_Prefix
import F3T_PrefixCongr
import F3T_Probability
import F3T_Projection
import F3T_ProofCarriers
import F3T_PublicExt
import F3T_Reached
import F3T_Recovered
import F3T_RootAgreement
import F3T_Roots
import F3T_Runtime
import F3T_RuntimeBound
import F3T_Semantic
import F3T_SemanticHead
import F3T_SourceCost
import F3T_SourcePair
import F3T_Tag
import F3T_Trace
import F3T_TwoPass
import F3T_Unrestricted

/-! Once-only focused candidate axioms audit; no release or adoption claim. -/
#print axioms AspisR1.F3T_AcceptedFacts.accepted_facts
#print axioms AspisR1.F3T_AcceptedParser.parsed
#print axioms AspisR1.F3T_AcceptedParser.tag
#print axioms AspisR1.F3T_AcceptedReplacement.program
#print axioms AspisR1.F3T_AcceptedTransport.original_eq
#print axioms AspisR1.F3T_AcceptedTransport.built_words
#print axioms AspisR1.F3T_AcceptedTransport.annotated_eq
#print axioms AspisR1.F3T_AccountCharge.reads
#print axioms AspisR1.F3T_AccountCharge.bound
#print axioms AspisR1.F3T_AccountSource.account_bound
#print axioms AspisR1.F3T_Accounting.first_reads
#print axioms AspisR1.F3T_Accounting.log_length
#print axioms AspisR1.F3T_Accounting.mass_projection
#print axioms AspisR1.F3T_ActualChecks.tail_root
#print axioms AspisR1.F3T_ActualChecks.middle_root
#print axioms AspisR1.F3T_ActualChecks.maps_eq_builder
#print axioms AspisR1.F3T_ActualChecks.accepted_checks
#print axioms AspisR1.F3T_Admission.physical
#print axioms AspisR1.F3T_Admission.semantic
#print axioms AspisR1.F3T_Admission.stored
#print axioms AspisR1.F3T_AlignedRows.lookup
#print axioms AspisR1.F3T_AlignedRows.initial
#print axioms AspisR1.F3T_AlignedRows.payload
#print axioms AspisR1.F3T_AlignedRows.canonical_rows
#print axioms AspisR1.F3T_Bounds.carriers
#print axioms AspisR1.F3T_Bounds.first_reads
#print axioms AspisR1.F3T_Bounds.distinct_bound
#print axioms AspisR1.F3T_Bounds.log_length
#print axioms AspisR1.F3T_ByteCarrier.lift_eval
#print axioms AspisR1.F3T_ByteCarrier.public_bytes
#print axioms AspisR1.F3T_ByteCarrier.stored_bytes
#print axioms AspisR1.F3T_ByteTag.public_tag
#print axioms AspisR1.F3T_ByteTag.semantic_tag
#print axioms AspisR1.F3T_ByteTransport.annotated_eq
#print axioms AspisR1.F3T_ByteTransport.recovered
#print axioms AspisR1.F3T_Canon.canon_eval
#print axioms AspisR1.F3T_Canon.verifier_canon
#print axioms AspisR1.F3T_Canon.acceptance
#print axioms AspisR1.F3T_Canon.bound
#print axioms AspisR1.F3T_CanonicalChecks.canonical_valid
#print axioms AspisR1.F3T_CanonicalChecks.rows_eq
#print axioms AspisR1.F3T_CanonicalChecks.accepted_checks
#print axioms AspisR1.F3T_CanonicalJoin.carried_join
#print axioms AspisR1.F3T_Carried.input_carried
#print axioms AspisR1.F3T_Carried.lift_carried
#print axioms AspisR1.F3T_Carried.enrich_carried
#print axioms AspisR1.F3T_Carried.canon_carried
#print axioms AspisR1.F3T_Carried.canon_lift_carried
#print axioms AspisR1.F3T_Causal.transcript_start_read
#print axioms AspisR1.F3T_Causal.transcript_start_prover_or_followed
#print axioms AspisR1.F3T_Causal.recovered_eval
#print axioms AspisR1.F3T_Charged.charged_eval
#print axioms AspisR1.F3T_Charged.projected_eval
#print axioms AspisR1.F3T_Charged.starts
#print axioms AspisR1.F3T_Checked.original_clean
#print axioms AspisR1.F3T_Clean.clean
#print axioms AspisR1.F3T_Combined.arithmetic
#print axioms AspisR1.F3T_Combined.model_and_account
#print axioms AspisR1.F3T_Combined.zero_queries
#print axioms AspisR1.F3T_Completion.decodes
#print axioms AspisR1.F3T_Completion.chains_read
#print axioms AspisR1.F3T_Completion.prefix_chain_read
#print axioms AspisR1.F3T_Completion.protocol_rounds
#print axioms AspisR1.F3T_Completion.hit_in_prefix
#print axioms AspisR1.F3T_Conditional.installed
#print axioms AspisR1.F3T_ConditionalClaims.claims
#print axioms AspisR1.F3T_ConditionalSum.bound
#print axioms AspisR1.F3T_ConditionalSum.zero_queries
#print axioms AspisR1.F3T_Cost.accepted_attempt_cost
#print axioms AspisR1.F3T_Cost.returned_relation
#print axioms AspisR1.F3T_Decision.after_value
#print axioms AspisR1.F3T_Decision.value
#print axioms AspisR1.F3T_Decision.admitted
#print axioms AspisR1.F3T_Decision.accepted_details
#print axioms AspisR1.F3T_Experiment.original_eval
#print axioms AspisR1.F3T_Experiment.verifier_enrich
#print axioms AspisR1.F3T_Experiment.compiled_eval
#print axioms AspisR1.F3T_Experiment.recorded_eval
#print axioms AspisR1.F3T_Frame.frame_eq
#print axioms AspisR1.F3T_HeadCanonical.program
#print axioms AspisR1.F3T_HeadCanonical.source_eval
#print axioms AspisR1.F3T_HeadCanonical.collision_or_source_eval
#print axioms AspisR1.F3T_InitFrame.public_bytes
#print axioms AspisR1.F3T_InitHead.head
#print axioms AspisR1.F3T_InitialConstructor.initial
#print axioms AspisR1.F3T_InputAgreement.from_source_rows
#print axioms AspisR1.F3T_Installed.physical
#print axioms AspisR1.F3T_Installed.annotation
#print axioms AspisR1.F3T_Installed.old_source
#print axioms AspisR1.F3T_Installed.installed
#print axioms AspisR1.F3T_InstalledRecovered.inputs
#print axioms AspisR1.F3T_InstalledRecovered.extractor
#print axioms AspisR1.F3T_JoinBoundary.accepted_eval
#print axioms AspisR1.F3T_JoinBoundary.collision_or_eval
#print axioms AspisR1.F3T_JoinBoundary.dropping_collision_invalid
#print axioms AspisR1.F3T_Leaves.apply_values
#print axioms AspisR1.F3T_ModelClaims.failure_bound
#print axioms AspisR1.F3T_ModelClaims.per_attempt
#print axioms AspisR1.F3T_ModelClaims.zero_queries
#print axioms AspisR1.F3T_Numeric.margin_exact
#print axioms AspisR1.F3T_Numeric.margin_positive
#print axioms AspisR1.F3T_Numeric.zero_queries
#print axioms AspisR1.F3T_ParsedRows.rows
#print axioms AspisR1.F3T_ParsedRows.bounds
#print axioms AspisR1.F3T_Prefix.same_transcript
#print axioms AspisR1.F3T_Prefix.chronological_prefix
#print axioms AspisR1.F3T_Prefix.first_start_before_terminal
#print axioms AspisR1.F3T_PrefixCongr.verifierFrom_congr
#print axioms AspisR1.F3T_PrefixCongr.verifier_congr
#print axioms AspisR1.F3T_Probability.hit_mass
#print axioms AspisR1.F3T_Probability.restricted_union_bound
#print axioms AspisR1.F3T_Probability.failure_bound
#print axioms AspisR1.F3T_Projection.project_eval
#print axioms AspisR1.F3T_Projection.original_view
#print axioms AspisR1.F3T_Projection.recorded_view
#print axioms AspisR1.F3T_ProofCarriers.payload_eq
#print axioms AspisR1.F3T_ProofCarriers.erased
#print axioms AspisR1.F3T_ProofCarriers.from_parse
#print axioms AspisR1.F3T_PublicExt.public_ext
#print axioms AspisR1.F3T_PublicExt.semantic_ext
#print axioms AspisR1.F3T_Reached.accepted
#print axioms AspisR1.F3T_Reached.decision_read
#print axioms AspisR1.F3T_Reached.slots_read
#print axioms AspisR1.F3T_Reached.consistent
#print axioms AspisR1.F3T_Reached.distinct_bound
#print axioms AspisR1.F3T_Reached.frame_read
#print axioms AspisR1.F3T_Recovered.inputs
#print axioms AspisR1.F3T_Recovered.extractor
#print axioms AspisR1.F3T_RootAgreement.from_bytes
#print axioms AspisR1.F3T_Roots.erased_index
#print axioms AspisR1.F3T_Roots.targets
#print axioms AspisR1.F3T_Runtime.nonnegative
#print axioms AspisR1.F3T_Runtime.transport
#print axioms AspisR1.F3T_RuntimeBound.failure_bound
#print axioms AspisR1.F3T_Semantic.publicOf_bytes
#print axioms AspisR1.F3T_Semantic.from_serialization
#print axioms AspisR1.F3T_SemanticHead.bytes
#print axioms AspisR1.F3T_SourceCost.accepted_attempt_cost
#print axioms AspisR1.F3T_SourcePair.accepted_pair
#print axioms AspisR1.F3T_Tag.base_tag
#print axioms AspisR1.F3T_Trace.accepted_trace
#print axioms AspisR1.F3T_Trace.old_read
#print axioms AspisR1.F3T_Trace.six_inserted
#print axioms AspisR1.F3T_TwoPass.original_eval
#print axioms AspisR1.F3T_TwoPass.compiled_eval
#print axioms AspisR1.F3T_TwoPass.annotated_eval
#print axioms AspisR1.F3T_Unrestricted.constant_rejected
#print axioms AspisR1.F3T_Unrestricted.no_global_join
