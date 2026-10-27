# Authentication association gap

Static inspection of the supplied Lean and extracted-source trees found no definition of decode_pool_v1_pair_forest_master_v1, decode_pool_v1_pair_forest_checkpoint_v1, decode_pool_v1_pair_forest_lane_state_v1, decode_verifier_registry_v2 or decode_verifier_registry_entry_v2. AdapterRwModel declares their wrapper slots op48/49/50 and registry slots op33/34 as abstract operations; op38 is the abstract SDK PDA child. This is missing source association, not a proof that the retained bytes reject, and not an authorized new trust item.

The Rust master decoder at crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs:261 fills last_checkpoint_lane_sequences via iter_mut().enumerate(). The checkpoint decoder and lane/tree decoder also require narrowed-D188 inspection/native differential. No extracted stand-in or expected-record callback may be silently substituted. JHj_ caller-stage work cannot discharge these child rows by itself.

Emission: JHi_EmissionAssociation.source proves op53 equals JHb_EmitAdapter.source, explicitly a return-data model. No native syscall/ELF association follows from that theorem. Existing narrowed-D188 caveats for terminal encoders, sampler, weights, query/flush and result stores remain.
