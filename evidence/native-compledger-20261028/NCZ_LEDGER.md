# Native composition ledger

Frozen source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`; merged evidence snapshot `1d7752908191642fc8383c99bbadfb46fab8850c`.
Headline `AspisR1.RPx_Deployed.deployed`. **The deployed 100-bit target remains unestablished.**

This is a machine-validated evidence ledger and conservative call-graph argument. It does not supply new native bridges or Lean caller-domain certificates. Owner amendment fifth is reported as a P6/D188 tool-trust reclassification, never premise removal.

| Inventory | Rows | Local conditional bridges | Local OPEN | Quarantined | Composed OPEN | Trust only |
|---|---:|---:|---:|---:|---:|---:|
| TX1 | 345 | 106 | 237 | 2 | 345 | 0 |
| TX2 | 242 | 107 | 133 | 2 | 242 | 0 |
| all_rows | 587 | 213 | 370 | 4 | 587 | 0 |

Unique functions: 434. Shared TX1/TX2 bodies count once only in the union graph; transaction rows keep separate edges/domains.

Every conditional bridge retains two named hypotheses: its exact packet domain and its physical interpretation. The original statement/qualifications appear verbatim in `claims[].source_claim_text` and the pinned packet. Every call edge has a named caller-owned domain obligation; absent same-execution discharge is explicitly OPEN. Inventory domain prose is a proposed obligation, never its proof. Model/extraction names alone earn no credit.

The ledger distinguishes reported historical labels, admissible local claims, quarantined support, replacements, feature parity and composed status. KNF restores local leaf support through static proofs without clearing historical pointer receipts. KNG supplies replacement properties for the 23 NCS unresolved associations; it does not widen their domains. KMX/KMZ copy windows and ambiguous multi-root claims remain fragments. The digest wrapper transports bytes; `RuntimeSha256Value` alone supplies its value law. Coherent digest/error slots are op43/op44.

## Critical path

In canonical conservative union graph choose one OPEN/quarantined representative from each terminal SCC under reachability between OPEN SCCs. This is a minimum-cardinality reachability cover of all OPEN functions, not a dynamic/runtime critical path or a sufficient proof set.

Every terminal open SCC needs its own representative; no other open SCC can be reached downstream from it. Every open SCC reaches a terminal open SCC.

**Inventory caveat:** conservative arithmetic carrier unions include self/cyclic edges (e.g. CM31::add). These are retained, not pruned by guessed types. Ranking is advisory until carrier resolution is proved. Closing the frontier still leaves callers, domain transport, effects and physical interpretation to prove.

| Highest-impact OPEN function | Other inventory rows depending on it |
|---|---:|
| `crates/aspis-core/src/field.rs::M31::reduce_u62` | 40 |
| `crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new` | 34 |
| `crates/aspis-r1-cost-probe/src/weights.rs::field` | 31 |
| `crates/aspis-core/src/field.rs::CM31::from_m31` | 29 |
| `crates/aspis-core/src/field.rs::qm31_pack_base4` | 29 |
| `crates/aspis-core/src/field.rs::CM31::square` | 28 |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::square` | 28 |
| `crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs` | 27 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits` | 26 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31` | 24 |

Minimum reachability-cover frontier: **133 SCC representatives**. Full members and all graph cycles are in JSON.

| Frontier representative | Dependent rows | OPEN functions in SCC |
|---|---:|---:|
| `crates/aspis-core/src/field.rs::M31::reduce_u62` | 40 | 1 |
| `crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new` | 34 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::field` | 31 | 1 |
| `crates/aspis-core/src/field.rs::CM31::from_m31` | 29 | 1 |
| `crates/aspis-core/src/field.rs::qm31_pack_base4` | 29 | 1 |
| `crates/aspis-core/src/field.rs::CM31::square` | 28 | 1 |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::square` | 28 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits` | 26 | 1 |
| `crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums` | 23 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::opening` | 23 | 1 |
| `crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs` | 23 | 1 |
| `crates/aspis-core/src/field.rs::CM31::neg` | 22 | 1 |
| `crates/aspis-core/src/field.rs::QM31::neg` | 22 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::index_at` | 22 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed` | 22 | 1 |
| `crates/aspis-core/src/field.rs::qm31_accumulate_product_channels` | 21 | 1 |
| `crates/aspis-r1-cost-probe/src/sampler.rs::qm31_div_pass` | 21 | 1 |
| `crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw` | 21 | 1 |
| `crates/aspis-core/src/r0/merkle.rs::parent_with_digest` | 20 | 1 |
| `crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/compact.rs::slot_offset` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/multiproof.rs::value_at` | 20 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row` | 20 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::empty_root` | 20 | 1 |
| `crates/aspis-core/src/r0/heap.rs::filled` | 19 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high` | 19 | 1 |
| `crates/aspis-core/src/r0/domain.rs::FibreIndex::get` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::mark` | 18 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::bounded_append_carry` | 18 | 1 |
| `crates/aspis-statement/src/poseidon2.rs::pow5` | 18 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record` | 17 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row` | 17 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_dot` | 17 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::initial_variant_selectors` | 17 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero` | 17 | 1 |
| `crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_limb` | 17 | 1 |
| `crates/aspis-core/src/field.rs::QM31::is_zero` | 16 | 1 |
| `crates/aspis-core/src/field.rs::qm31_m31_dot` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::framed` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses` | 16 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active_mask_basis` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_pattern_basis_values` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::selected_binary_weight` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::reconstruct_10` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::variant_expected_output` | 16 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_residual` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::link_weight` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::private_public` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::scalar_lanes` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::withdrawal_public` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot` | 15 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot` | 15 | 1 |
| `crates/aspis-core/src/field.rs::M31::neg` | 14 | 1 |
| `crates/aspis-core/src/field/wide_exact.rs::WideExact::neg` | 14 | 1 |
| `crates/aspis-core/src/r0/domain.rs::FibreIndex::new` | 14 | 1 |
| `crates/aspis-core/src/r0_transcript.rs::block_rank` | 14 | 1 |
| `crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::absorb` | 14 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products` | 14 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor` | 14 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::copy_variant` | 14 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::selected_claim` | 14 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner` | 14 | 1 |
| `crates/aspis-core/src/state_only_hiding.rs::cm31_mul_r` | 13 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_value` | 13 | 1 |
| `crates/aspis-r1-cost-probe/src/sampler.rs::decode8` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::equality_value` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::fields` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable` | 13 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable` | 13 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key` | 13 | 1 |
| `crates/aspis-core/src/r0_transcript.rs::QueryScan::finish` | 12 | 1 |
| `crates/aspis-core/src/state_only_hiding.rs::selected_mask_linears` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/sampler.rs::add_small_base_p` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish` | 12 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor` | 12 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_live_snapshot_v1` | 12 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok` | 12 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len` | 12 | 1 |
| `crates/aspis-core/src/state_only_prefix.rs::state_only_statement_points` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::new` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::high_dot` | 11 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_afterstate_boxed_v1` | 11 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from` | 11 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data` | 11 | 1 |
| `crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::new` | 10 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts` | 10 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::double` | 10 | 1 |
| `crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard` | 10 | 1 |
| `crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1` | 10 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok` | 10 | 1 |
| `crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic` | 9 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::raw` | 9 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_semantic_alpha` | 9 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_weights` | 9 | 1 |
| `crates/aspis-r1-cost-probe/src/verifier.rs::validate_checkpoint_queries` | 9 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1` | 9 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused` | 9 | 1 |
| `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused` | 9 | 1 |
| `programs/r1-cost-probe/src/lib.rs::observer` | 9 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id` | 9 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id` | 9 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_transfer_statement_boxed_v1` | 8 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_withdrawal_statement_boxed_v1` | 8 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::asq8_common` | 8 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release` | 8 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box` | 8 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box` | 8 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1` | 7 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1` | 7 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1` | 7 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer` | 7 | 1 |
| `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public` | 6 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero` | 6 | 1 |
| `programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot` | 6 | 1 |
| `programs/r1-cost-probe/src/pool_route.rs::admitted` | 2 | 1 |

## Reproduction and boundaries

`python3 evidence/native-compledger-20261028/NCZ_validate.py` recomputes bodies, edges, claims, feature/re-credit overlays, receipt hashes, coverage and frontier, then compares the entire ledger and this summary. `--write` deliberately regenerates derived files; it does not make new evidence pass. Present sparse-worktree files must match the pinned Git blobs, and tracked deletions fail. Unmaterialized sparse files are read from immutable Git objects. Each cited artifact is SHA256-pinned. New/changed merged reports require an explicit refreshed snapshot; no silent credit from later branches.

Discovery searched **5215** top-level merged/legacy evidence and design reports. Documentary mentions are discovery pointers, not semantic adoption. Unindexed CLOSED mentions and unresolved historical reference pointers are retained in JSON for audit; an unresolved pointer is never presented as a valid citation. Every cited row artifact must exist and match. The validator checks indexed evidence consistency; it is not a natural-language theorem prover and cannot detect a contradiction hidden in arbitrary new prose without an explicit evidence/schema update.

No Rust/Lean/Kani/SBF job ran; no new theorem or axioms. 0/10 Lean status attempts, 0/0 Kani. No shipped files changed, so ELF rebuild was not triggered. No host/cache/key operation. Prior ELF pins remain inherited, not reproduced.
