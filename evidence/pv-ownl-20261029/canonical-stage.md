# Canonicality stage limits

Scale.canonical has no operand bounds, including on inverse. HelperSlots/HelperRows propagate this through every nonzero-weight contribution and early pole failure, then through the source-selected Vec helper or host array stores. InputBytes.read_write is an all-u32 roundtrip, and checked_iff relates acceptance of that representation to exact limb bounds. SampleWord proves the remainder/cast invariant; SampleCanon uses a source-shaped quotient-store state fold and needs no rank-reduction property.

The consuming path selects statement pair_forest_semantic_oracle -> logup::build_copy_logup_helper, not prover host_forest's array helper. Both are explicitly distinguished. The actual transcript selects core r0_transcript, not the cost-probe sampler.

Inputs.accepted_columns is a successful model-input composition; the generic helper parameter's canonicality is no longer a premise. This is not a proof that the actual complete byte/array/ownership execution satisfies that model. Error tags and framing/array carriers remain source-refinement work. The native differential is finite validation; ordered-token checks alone do not close that work.
