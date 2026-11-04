# NFK authoritative ledger

Target not yet established. Conditional source composition; no cold release or whole headline replay.

The exact NEZ 202/587 checkpoint is retained and extended using immutable successful receipts. NFJ inputs come from merged commit `eeaa04cfaf3`: HEAD `9905ea55a106eadbf120088a8b7601c6fa7c2843` removed that evidence directory. This refresh records the historical merge explicitly. No Lean, Kani or native build ran.

| Scope | Total | CLOSED | QUALIFIED | OPEN |
|---|---:|---:|---:|---:|
| all_rows | 587 | 219 | 2 | 366 |
| TX1 | 345 | 107 | 1 | 237 |
| TX2 | 242 | 112 | 1 | 129 |
| slice Q (overlapping membership) | 149 | 126 | 2 | 21 |
| Q TX1 | 78 | 63 | 1 | 14 |
| Q TX2 | 71 | 63 | 1 | 7 |
| slice S (overlapping membership) | 97 | 97 | 0 | 0 |
| S TX1 | 46 | 46 | 0 | 0 |
| S TX2 | 51 | 51 | 0 | 0 |

Unique functions: {"fully_CLOSED": 122, "total": 434, "with_CLOSED_occurrence": 122, "with_QUALIFIED_occurrence": 1}. Slice overlap is counted once globally. Per-function counts and rows follow below.

## Roots

Slice Q: 0/2 roots CLOSED; 63 fully CLOSED unique functions.
- `crates/aspis-r1-cost-probe/src/candidate.rs::query_loop`: OPEN (TX1:088, TX2:058).
- `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range`: QUALIFIED (TX1:181, TX2:104).
Slice S: 7/7 roots CLOSED; 61 fully CLOSED unique functions.
- `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box`: CLOSED (TX1:332).
- `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1`: CLOSED (TX1:276, TX2:169).
- `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1`: CLOSED (TX2:165).
- `programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement`: CLOSED (TX2:224).
- `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1`: CLOSED (TX2:163).
- `programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer`: CLOSED (TX2:226).
- `programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result`: CLOSED (TX2:219).

## Added runtime trust (owner confirmation pending)

- RuntimeMemcmp: 1 CLOSED, 0 QUALIFIED, 0 OPEN occurrences. Rows: TX2:226. ADDED trust; owner confirmation pending.
- RuntimeReturnData: 1 CLOSED, 0 QUALIFIED, 0 OPEN occurrences. Rows: TX2:219. ADDED trust; owner confirmation pending.

These runtime rows are additions, not discharged cryptographic or native implementation obligations. Rejecting (ab) reopens emit_result; rejecting (ac) reopens scan_proof_buffer. Pool return-data association remains separately OPEN.

## Rejected slice-reported CLOSED rows

- TX1:181 `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range`: QUALIFIED; reported by NFB; Source-validator CLOSED; headline import duplicates verifier.Phase (NFF_FINDINGS.md L032); coherent retarget replay not in this pinned refresh
- TX2:104 `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range`: QUALIFIED; reported by NFB; Source-validator CLOSED; headline import duplicates verifier.Phase (NFF_FINDINGS.md L032); coherent retarget replay not in this pinned refresh

NFA withholds admission; NFC admits exactly the four inherited NEV rows after ax2. NEW/NFB and NFE/NFF cumulative reports overlap these rows; their totals are never added together. Historical NEZ slice rejections remain included.

## Exact function coverage

| Function | Occurrences | CLOSED | QUALIFIED | OPEN |
|---|---:|---:|---:|---:|
| crates/aspis-core/src/field.rs::CM31::add | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::CM31::double | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::CM31::from_le_bytes | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::CM31::from_m31 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::CM31::inv | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::CM31::inv_with | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::CM31::mul | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::CM31::mul_m31 | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::CM31::neg | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::CM31::new | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::CM31::square | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::CM31::sub | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::CM31::write_le_bytes | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::M31::add | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::M31::double | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::M31::from_le_bytes | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::M31::inv | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::M31::mul | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::M31::neg | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::M31::reduce_u62 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::M31::reduce_u64 | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::M31::sub | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::M31::to_le_bytes | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::QM31::add | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::QM31::from_cm31 | 2 | 0 | 0 | 2 |
| crates/aspis-core/src/field.rs::QM31::from_le_bytes | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::QM31::inv | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::QM31::is_zero | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::QM31::mul | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::QM31::mul_m31 | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::QM31::neg | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::QM31::square | 2 | 0 | 0 | 2 |
| crates/aspis-core/src/field.rs::QM31::sub | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::QM31::try_inv | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::QM31::write_le_bytes | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::mul_by_r | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::qm31_accumulate_product_channels | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::qm31_m31_dot | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::qm31_pack_base4 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::qm31_sum_products2 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::qm31_sum_products3 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::qm31_sum_products3_prepared | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::qm31_sum_products4 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::qm31_sum_products_small | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field.rs::reduce_u64 | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field.rs::square_n | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::add | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::c0 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::c1 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31 | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::mul | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::neg | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::new | 2 | 0 | 0 | 2 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::square | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::sub | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::canonical_qm31 | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/field/wide_exact.rs::mul_u | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/r0/domain.rs::FibreIndex::get | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/r0/domain.rs::FibreIndex::new | 2 | 2 | 0 | 0 |
| crates/aspis-core/src/r0/heap.rs::filled | 2 | 0 | 0 | 2 |
| crates/aspis-core/src/r0/merkle.rs::parent_with_digest | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/r0_transcript.rs::QueryScan::finish | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/r0_transcript.rs::QueryScan::scan | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/r0_transcript.rs::block_rank | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/r0_transcript.rs::queries_from_pairs | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/r0_transcript.rs::query_words | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/state_only_hiding.rs::cm31_mul_i | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/state_only_hiding.rs::cm31_mul_r | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/state_only_hiding.rs::mask_power_26 | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/state_only_hiding.rs::mul_tower_basis | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/state_only_hiding.rs::selected_mask_linears | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/state_only_hiding.rs::state_only_selected_mask_value | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/state_only_prefix.rs::r0::statement_points | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/state_only_prefix.rs::state_only_statement_points | 1 | 0 | 0 | 1 |
| crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::batch_leaf | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle_values | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::canonical_scan | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/candidate.rs::opening | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::prepare | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/candidate.rs::query_loop | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::query_values | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::slot | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/candidate.rs::tx1 | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/candidate.rs::wide_view | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/compact.rs::check_values | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/compact.rs::compact_row | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/compact.rs::expand_values | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/compact.rs::slot_offset | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_domain.rs::line_node | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::finish | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_limbs | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_wide | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::limbs | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::reduce | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::checked_q | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/fast_pairing.rs::limbs_of | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::index_at | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::node_count | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::value_at | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs::claims | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs::public_transcript | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_boundary | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_round | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_rounds | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_value | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_finish | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::parse | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::payload | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::circle_validated | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::new | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::semantic_validated | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::framed | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::begin | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record_at | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/sampler.rs::add_small_base_p | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/sampler.rs::circle_sample | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/sampler.rs::decode8 | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/sampler.rs::gamma_sample | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/sampler.rs::low_base_p_digits | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/sampler.rs::ordinary_sample | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/sampler.rs::qm31_digits | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/sampler.rs::qm31_div_pass | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/sampler.rs::qm31_sample | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/trace.rs::value | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::absorb | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::block | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::new | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar_k | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/transport.rs::Variant::folds | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::Accumulator::new | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::push | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range | 2 | 0 | 2 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::e | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::k | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::raw | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::accumulated_weight_at | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::basis_at | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::echeck | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation_round | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::mark | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::polynomial | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::power_limb_at | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_semantic_alpha | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_weights | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::residue_limb_at | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::resume | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/verifier.rs::validate_checkpoint_queries | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::Weights::new | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::Weights::pair | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::double | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::factored_s2_libra_weights | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::field | 2 | 2 | 0 | 0 |
| crates/aspis-r1-cost-probe/src/weights.rs::grouped_inactive_pair | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::high_dot | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::partial_dot | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::powers | 2 | 0 | 0 | 2 |
| crates/aspis-r1-cost-probe/src/weights.rs::process_kind | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::process_regular_kinds | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::push_byte_products | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::s2_grouped_inactive_pair | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::shared_high | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::shared_partials | 1 | 0 | 0 | 1 |
| crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/atomic_statement.rs::unwrap_fixed_slice | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/format.rs::decode_verifier_policy_v1 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/format.rs::pool_v1_tree_parent | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::default | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::empty | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/incremental_merkle.rs::pool_v1_empty_roots | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::validate_master | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active_mask_basis | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::at_point | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::boxed_at_point | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::expand | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::accumulate_endpoint_selector_tensor_basis | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_residual | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_dot | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_value | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::evaluate_with_selectors | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_pattern_basis_values | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_selector_tensor_basis | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::link_weight | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values_windowed | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::qm31_sum_products_up_to4 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::selected_binary_weight | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::absorption_lanes_factored | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_occupancy_lanes | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_path_lanes | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted_shared_selector | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_schedule_lanes | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_value_lanes | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_level_packed_selector_tensor | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_levels_packed_selector_tensor | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::bounded_append_carry | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::composition_parts | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::copy_variant | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::empty_root | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::equality_value | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::initial_variant_selectors | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::left_digest_packed_selector_tensor | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::occupancy_lanes_factored | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_carry_packed_selector_tensor | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_recipient_packed_selector_tensor | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::path_lanes_factored | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::poseidon_selectors | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::private_public | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed_selector_tensor | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::fields | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::frontier | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::semantic | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::terminal_qm31 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::reconstruct_10 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::scalar_lanes | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::selected_claim | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_initial_and_absorption | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_packed | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::terminal_parts | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::validate_transition | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::variant_expected_output | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::withdrawal_public | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::transition_kind | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_lane_transition_boxed_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_statement_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_terminal_common_boxed_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_transfer_statement_boxed_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_withdrawal_statement_boxed_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::statement_public_common | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_result | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_afterstate_boxed_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_live_snapshot_boxed_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_late_public_statement_boxed_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_live_snapshot_v1 | 1 | 1 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::require_header | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::transfer_common | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1 | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/payment_relation.rs::withdrawal_common | 2 | 2 | 0 | 0 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v1 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v2 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v1 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v2 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/poseidon2.rs::external_linear_lazy | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/poseidon2.rs::merkle_node_compress_v3 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/poseidon2.rs::pow5 | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::evaluate_state_only_poseidon_oracle_projected | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::external_linear_lazy | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::external_linear_packed | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::full_round | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants_packed | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::full_round_packed | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::internal_linear_lazy | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::internal_round | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_columns | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_limb | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::interpolated_full_pair_packed | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::interpolated_internal_pair | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::leading_pair_packed | 1 | 0 | 0 | 1 |
| crates/aspis-statement/src/state_only_poseidon.rs::pow5 | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/lib.rs::error | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/lib.rs::first_decoded | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/lib.rs::observer | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/pool_route.rs::admitted | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::asq8_common | 1 | 1 | 0 | 0 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box | 1 | 1 | 0 | 0 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result | 1 | 1 | 0 | 0 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::process | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement | 1 | 1 | 0 | 0 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer | 1 | 1 | 0 | 0 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box | 1 | 1 | 0 | 0 |
| programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box | 1 | 1 | 0 | 0 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot | 2 | 0 | 0 | 2 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1 | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2 | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned | 1 | 0 | 0 | 1 |
| programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8 | 1 | 0 | 0 | 1 |

## Every occurrence

| Row | Function | Status | Added trust | Reason |
|---|---|---|---|---|
| TX1:001 | crates/aspis-core/src/field.rs::CM31::add | CLOSED |  |  |
| TX1:002 | crates/aspis-core/src/field.rs::CM31::double | CLOSED |  |  |
| TX1:003 | crates/aspis-core/src/field.rs::CM31::from_le_bytes | CLOSED |  |  |
| TX1:004 | crates/aspis-core/src/field.rs::CM31::from_m31 | OPEN |  |  |
| TX1:005 | crates/aspis-core/src/field.rs::CM31::inv | OPEN |  |  |
| TX1:006 | crates/aspis-core/src/field.rs::CM31::inv_with | OPEN |  |  |
| TX1:007 | crates/aspis-core/src/field.rs::CM31::mul | CLOSED |  |  |
| TX1:008 | crates/aspis-core/src/field.rs::CM31::mul_m31 | CLOSED |  |  |
| TX1:009 | crates/aspis-core/src/field.rs::CM31::neg | OPEN |  |  |
| TX1:010 | crates/aspis-core/src/field.rs::CM31::new | CLOSED |  |  |
| TX1:011 | crates/aspis-core/src/field.rs::CM31::square | OPEN |  |  |
| TX1:012 | crates/aspis-core/src/field.rs::CM31::sub | CLOSED |  |  |
| TX1:013 | crates/aspis-core/src/field.rs::M31::add | CLOSED |  |  |
| TX1:014 | crates/aspis-core/src/field.rs::M31::double | CLOSED |  |  |
| TX1:015 | crates/aspis-core/src/field.rs::M31::from_le_bytes | CLOSED |  |  |
| TX1:016 | crates/aspis-core/src/field.rs::M31::inv | CLOSED |  |  |
| TX1:017 | crates/aspis-core/src/field.rs::M31::mul | CLOSED |  |  |
| TX1:018 | crates/aspis-core/src/field.rs::M31::neg | OPEN |  |  |
| TX1:019 | crates/aspis-core/src/field.rs::M31::reduce_u62 | OPEN |  |  |
| TX1:020 | crates/aspis-core/src/field.rs::M31::reduce_u64 | CLOSED |  |  |
| TX1:021 | crates/aspis-core/src/field.rs::M31::sub | CLOSED |  |  |
| TX1:022 | crates/aspis-core/src/field.rs::M31::to_le_bytes | CLOSED |  |  |
| TX1:023 | crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new | OPEN |  |  |
| TX1:024 | crates/aspis-core/src/field.rs::QM31::add | CLOSED |  |  |
| TX1:025 | crates/aspis-core/src/field.rs::QM31::from_cm31 | OPEN |  |  |
| TX1:026 | crates/aspis-core/src/field.rs::QM31::from_le_bytes | CLOSED |  |  |
| TX1:027 | crates/aspis-core/src/field.rs::QM31::inv | OPEN |  |  |
| TX1:028 | crates/aspis-core/src/field.rs::QM31::is_zero | OPEN |  |  |
| TX1:029 | crates/aspis-core/src/field.rs::QM31::mul | CLOSED |  |  |
| TX1:030 | crates/aspis-core/src/field.rs::QM31::mul_m31 | CLOSED |  |  |
| TX1:031 | crates/aspis-core/src/field.rs::QM31::neg | OPEN |  |  |
| TX1:032 | crates/aspis-core/src/field.rs::QM31::square | OPEN |  |  |
| TX1:033 | crates/aspis-core/src/field.rs::QM31::sub | CLOSED |  |  |
| TX1:034 | crates/aspis-core/src/field.rs::QM31::try_inv | OPEN |  |  |
| TX1:035 | crates/aspis-core/src/field.rs::mul_by_r | CLOSED |  |  |
| TX1:036 | crates/aspis-core/src/field.rs::qm31_accumulate_product_channels | OPEN |  |  |
| TX1:037 | crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums | OPEN |  |  |
| TX1:038 | crates/aspis-core/src/field.rs::qm31_m31_dot | OPEN |  |  |
| TX1:039 | crates/aspis-core/src/field.rs::qm31_pack_base4 | OPEN |  |  |
| TX1:040 | crates/aspis-core/src/field.rs::qm31_sum_products2 | OPEN |  |  |
| TX1:041 | crates/aspis-core/src/field.rs::qm31_sum_products3 | OPEN |  |  |
| TX1:042 | crates/aspis-core/src/field.rs::qm31_sum_products3_prepared | OPEN |  |  |
| TX1:043 | crates/aspis-core/src/field.rs::qm31_sum_products4 | OPEN |  |  |
| TX1:044 | crates/aspis-core/src/field.rs::qm31_sum_products_small | OPEN |  |  |
| TX1:045 | crates/aspis-core/src/field.rs::reduce_u64 | CLOSED |  |  |
| TX1:046 | crates/aspis-core/src/field.rs::square_n | CLOSED |  |  |
| TX1:047 | crates/aspis-core/src/field/wide_exact.rs::WideExact::add | CLOSED |  |  |
| TX1:048 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes | CLOSED |  |  |
| TX1:049 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs | CLOSED |  |  |
| TX1:050 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31 | CLOSED |  |  |
| TX1:051 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul | CLOSED |  |  |
| TX1:052 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 | CLOSED |  |  |
| TX1:053 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 | CLOSED |  |  |
| TX1:054 | crates/aspis-core/src/field/wide_exact.rs::WideExact::neg | OPEN |  |  |
| TX1:055 | crates/aspis-core/src/field/wide_exact.rs::WideExact::new | OPEN |  |  |
| TX1:056 | crates/aspis-core/src/field/wide_exact.rs::WideExact::square | OPEN |  |  |
| TX1:057 | crates/aspis-core/src/field/wide_exact.rs::WideExact::sub | CLOSED |  |  |
| TX1:058 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes | CLOSED |  |  |
| TX1:059 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs | CLOSED |  |  |
| TX1:060 | crates/aspis-core/src/field/wide_exact.rs::canonical_qm31 | CLOSED |  |  |
| TX1:061 | crates/aspis-core/src/field/wide_exact.rs::mul_u | CLOSED |  |  |
| TX1:062 | crates/aspis-core/src/r0/domain.rs::FibreIndex::get | CLOSED |  |  |
| TX1:063 | crates/aspis-core/src/r0/domain.rs::FibreIndex::new | CLOSED |  |  |
| TX1:064 | crates/aspis-core/src/r0/heap.rs::filled | OPEN |  |  |
| TX1:065 | crates/aspis-core/src/r0/merkle.rs::parent_with_digest | OPEN |  |  |
| TX1:066 | crates/aspis-core/src/r0_transcript.rs::QueryScan::finish | OPEN |  |  |
| TX1:067 | crates/aspis-core/src/r0_transcript.rs::QueryScan::scan | OPEN |  |  |
| TX1:068 | crates/aspis-core/src/r0_transcript.rs::block_rank | OPEN |  |  |
| TX1:069 | crates/aspis-core/src/r0_transcript.rs::queries_from_pairs | OPEN |  |  |
| TX1:070 | crates/aspis-core/src/r0_transcript.rs::query_words | OPEN |  |  |
| TX1:071 | crates/aspis-core/src/state_only_hiding.rs::cm31_mul_i | OPEN |  |  |
| TX1:072 | crates/aspis-core/src/state_only_hiding.rs::cm31_mul_r | OPEN |  |  |
| TX1:073 | crates/aspis-core/src/state_only_hiding.rs::mask_power_26 | OPEN |  |  |
| TX1:074 | crates/aspis-core/src/state_only_hiding.rs::mul_tower_basis | OPEN |  |  |
| TX1:075 | crates/aspis-core/src/state_only_hiding.rs::selected_mask_linears | OPEN |  |  |
| TX1:076 | crates/aspis-core/src/state_only_hiding.rs::state_only_selected_mask_value | OPEN |  |  |
| TX1:077 | crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest | OPEN |  |  |
| TX1:078 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at | OPEN |  |  |
| TX1:079 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys | OPEN |  |  |
| TX1:080 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_leaf | OPEN |  |  |
| TX1:081 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle | OPEN |  |  |
| TX1:082 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle_values | OPEN |  |  |
| TX1:083 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree | OPEN |  |  |
| TX1:084 | crates/aspis-r1-cost-probe/src/candidate.rs::canonical_scan | OPEN |  |  |
| TX1:085 | crates/aspis-r1-cost-probe/src/candidate.rs::opening | CLOSED |  |  |
| TX1:086 | crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape | OPEN |  |  |
| TX1:087 | crates/aspis-r1-cost-probe/src/candidate.rs::prepare | OPEN |  |  |
| TX1:088 | crates/aspis-r1-cost-probe/src/candidate.rs::query_loop | OPEN |  |  |
| TX1:089 | crates/aspis-r1-cost-probe/src/candidate.rs::query_values | OPEN |  |  |
| TX1:090 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index | OPEN |  |  |
| TX1:091 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf | OPEN |  |  |
| TX1:092 | crates/aspis-r1-cost-probe/src/candidate.rs::slot | OPEN |  |  |
| TX1:093 | crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys | OPEN |  |  |
| TX1:094 | crates/aspis-r1-cost-probe/src/candidate.rs::tx1 | OPEN |  |  |
| TX1:095 | crates/aspis-r1-cost-probe/src/candidate.rs::wide_view | OPEN |  |  |
| TX1:096 | crates/aspis-r1-cost-probe/src/compact.rs::check_values | OPEN |  |  |
| TX1:097 | crates/aspis-r1-cost-probe/src/compact.rs::compact_row | OPEN |  |  |
| TX1:098 | crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic | OPEN |  |  |
| TX1:099 | crates/aspis-r1-cost-probe/src/compact.rs::expand_values | OPEN |  |  |
| TX1:100 | crates/aspis-r1-cost-probe/src/compact.rs::slot_offset | OPEN |  |  |
| TX1:101 | crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point | CLOSED |  |  |
| TX1:102 | crates/aspis-r1-cost-probe/src/fast_domain.rs::line_node | CLOSED |  |  |
| TX1:103 | crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value | CLOSED |  |  |
| TX1:104 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots | OPEN |  |  |
| TX1:105 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one | OPEN |  |  |
| TX1:106 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish | CLOSED |  |  |
| TX1:107 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new | CLOSED |  |  |
| TX1:108 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push | OPEN |  |  |
| TX1:109 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::finish | CLOSED |  |  |
| TX1:110 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new | CLOSED |  |  |
| TX1:111 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push | OPEN |  |  |
| TX1:112 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_limbs | CLOSED |  |  |
| TX1:113 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_wide | CLOSED |  |  |
| TX1:114 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::limbs | CLOSED |  |  |
| TX1:115 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::reduce | CLOSED |  |  |
| TX1:116 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::checked_q | CLOSED |  |  |
| TX1:117 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::limbs_of | CLOSED |  |  |
| TX1:118 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits | OPEN |  |  |
| TX1:119 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels | OPEN |  |  |
| TX1:120 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width | OPEN |  |  |
| TX1:121 | crates/aspis-r1-cost-probe/src/multiproof.rs::index_at | OPEN |  |  |
| TX1:122 | crates/aspis-r1-cost-probe/src/multiproof.rs::node_count | OPEN |  |  |
| TX1:123 | crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent | OPEN |  |  |
| TX1:124 | crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches | OPEN |  |  |
| TX1:125 | crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent | OPEN |  |  |
| TX1:126 | crates/aspis-r1-cost-probe/src/multiproof.rs::value_at | OPEN |  |  |
| TX1:127 | crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place | OPEN |  |  |
| TX1:128 | crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed | OPEN |  |  |
| TX1:129 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::claims | OPEN |  |  |
| TX1:130 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark | OPEN |  |  |
| TX1:131 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::public_transcript | OPEN |  |  |
| TX1:132 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_boundary | OPEN |  |  |
| TX1:133 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_round | OPEN |  |  |
| TX1:134 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_rounds | OPEN |  |  |
| TX1:135 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_value | OPEN |  |  |
| TX1:136 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_finish | OPEN |  |  |
| TX1:137 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed | OPEN |  |  |
| TX1:138 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::parse | OPEN |  |  |
| TX1:139 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::payload | OPEN |  |  |
| TX1:140 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record | OPEN |  |  |
| TX1:141 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record | OPEN |  |  |
| TX1:142 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::circle_validated | OPEN |  |  |
| TX1:143 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::new | OPEN |  |  |
| TX1:144 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated | OPEN |  |  |
| TX1:145 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::semantic_validated | OPEN |  |  |
| TX1:146 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state | OPEN |  |  |
| TX1:147 | crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k | OPEN |  |  |
| TX1:148 | crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::framed | OPEN |  |  |
| TX1:149 | crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row | OPEN |  |  |
| TX1:150 | crates/aspis-r1-cost-probe/src/r1_wire.rs::begin | OPEN |  |  |
| TX1:151 | crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record | OPEN |  |  |
| TX1:152 | crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record_at | OPEN |  |  |
| TX1:153 | crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape | OPEN |  |  |
| TX1:154 | crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields | OPEN |  |  |
| TX1:155 | crates/aspis-r1-cost-probe/src/sampler.rs::add_small_base_p | OPEN |  |  |
| TX1:156 | crates/aspis-r1-cost-probe/src/sampler.rs::circle_sample | OPEN |  |  |
| TX1:157 | crates/aspis-r1-cost-probe/src/sampler.rs::decode8 | OPEN |  |  |
| TX1:158 | crates/aspis-r1-cost-probe/src/sampler.rs::gamma_sample | OPEN |  |  |
| TX1:159 | crates/aspis-r1-cost-probe/src/sampler.rs::low_base_p_digits | OPEN |  |  |
| TX1:160 | crates/aspis-r1-cost-probe/src/sampler.rs::ordinary_sample | OPEN |  |  |
| TX1:161 | crates/aspis-r1-cost-probe/src/sampler.rs::qm31_digits | OPEN |  |  |
| TX1:162 | crates/aspis-r1-cost-probe/src/sampler.rs::qm31_div_pass | OPEN |  |  |
| TX1:163 | crates/aspis-r1-cost-probe/src/sampler.rs::qm31_sample | OPEN |  |  |
| TX1:164 | crates/aspis-r1-cost-probe/src/trace.rs::value | CLOSED |  |  |
| TX1:165 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::absorb | OPEN |  |  |
| TX1:166 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::block | OPEN |  |  |
| TX1:167 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::new | OPEN |  |  |
| TX1:168 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries | OPEN |  |  |
| TX1:169 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar | OPEN |  |  |
| TX1:170 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar_k | OPEN |  |  |
| TX1:171 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len | OPEN |  |  |
| TX1:172 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::folds | OPEN |  |  |
| TX1:173 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag | CLOSED |  |  |
| TX1:174 | crates/aspis-r1-cost-probe/src/verifier.rs::Accumulator::new | OPEN |  |  |
| TX1:175 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish | OPEN |  |  |
| TX1:176 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new | OPEN |  |  |
| TX1:177 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::push | CLOSED |  |  |
| TX1:178 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value | OPEN |  |  |
| TX1:179 | crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new | OPEN |  |  |
| TX1:180 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query | CLOSED |  |  |
| TX1:181 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range | QUALIFIED |  | Source-validator CLOSED; headline import duplicates verifier.Phase (NFF_FINDINGS.md L032); coherent retarget replay not in this pinned refresh |
| TX1:182 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node | CLOSED |  |  |
| TX1:183 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulated_weight_at | CLOSED |  |  |
| TX1:184 | crates/aspis-r1-cost-probe/src/verifier.rs::basis_at | CLOSED |  |  |
| TX1:185 | crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products | CLOSED |  |  |
| TX1:186 | crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint | OPEN |  |  |
| TX1:187 | crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size | OPEN |  |  |
| TX1:188 | crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses | CLOSED |  |  |
| TX1:189 | crates/aspis-r1-cost-probe/src/verifier.rs::echeck | OPEN |  |  |
| TX1:190 | crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses | CLOSED |  |  |
| TX1:191 | crates/aspis-r1-cost-probe/src/verifier.rs::mark | CLOSED |  |  |
| TX1:192 | crates/aspis-r1-cost-probe/src/verifier.rs::power_limb_at | CLOSED |  |  |
| TX1:193 | crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim | OPEN |  |  |
| TX1:194 | crates/aspis-r1-cost-probe/src/verifier.rs::residue_limb_at | CLOSED |  |  |
| TX1:195 | crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row | CLOSED |  |  |
| TX1:196 | crates/aspis-r1-cost-probe/src/weights.rs::field | CLOSED |  |  |
| TX1:197 | crates/aspis-r1-cost-probe/src/weights.rs::powers | OPEN |  |  |
| TX1:198 | crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical | CLOSED |  |  |
| TX1:199 | crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical | CLOSED |  |  |
| TX1:200 | crates/aspis-statement/src/atomic_statement.rs::unwrap_fixed_slice | CLOSED |  |  |
| TX1:201 | crates/aspis-statement/src/pool_v1/format.rs::pool_v1_tree_parent | OPEN |  |  |
| TX1:202 | crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::default | OPEN |  |  |
| TX1:203 | crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::empty | OPEN |  |  |
| TX1:204 | crates/aspis-statement/src/pool_v1/incremental_merkle.rs::pool_v1_empty_roots | OPEN |  |  |
| TX1:205 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical | CLOSED |  |  |
| TX1:206 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte | CLOSED |  |  |
| TX1:207 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 | CLOSED |  |  |
| TX1:208 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active | OPEN |  |  |
| TX1:209 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active_mask_basis | OPEN |  |  |
| TX1:210 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::at_point | OPEN |  |  |
| TX1:211 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::boxed_at_point | OPEN |  |  |
| TX1:212 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::expand | OPEN |  |  |
| TX1:213 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row | OPEN |  |  |
| TX1:214 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::accumulate_endpoint_selector_tensor_basis | OPEN |  |  |
| TX1:215 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_residual | OPEN |  |  |
| TX1:216 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_dot | OPEN |  |  |
| TX1:217 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_value | OPEN |  |  |
| TX1:218 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::evaluate_with_selectors | OPEN |  |  |
| TX1:219 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_pattern_basis_values | OPEN |  |  |
| TX1:220 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_selector_tensor_basis | OPEN |  |  |
| TX1:221 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31 | OPEN |  |  |
| TX1:222 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::link_weight | OPEN |  |  |
| TX1:223 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values | OPEN |  |  |
| TX1:224 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values_windowed | OPEN |  |  |
| TX1:225 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::qm31_sum_products_up_to4 | OPEN |  |  |
| TX1:226 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::selected_binary_weight | OPEN |  |  |
| TX1:227 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::absorption_lanes_factored | OPEN |  |  |
| TX1:228 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_occupancy_lanes | OPEN |  |  |
| TX1:229 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_path_lanes | OPEN |  |  |
| TX1:230 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted | OPEN |  |  |
| TX1:231 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted_shared_selector | OPEN |  |  |
| TX1:232 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_schedule_lanes | OPEN |  |  |
| TX1:233 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_value_lanes | OPEN |  |  |
| TX1:234 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_level_packed_selector_tensor | OPEN |  |  |
| TX1:235 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_levels_packed_selector_tensor | OPEN |  |  |
| TX1:236 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::bounded_append_carry | OPEN |  |  |
| TX1:237 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::composition_parts | OPEN |  |  |
| TX1:238 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::copy_variant | OPEN |  |  |
| TX1:239 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::empty_root | OPEN |  |  |
| TX1:240 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::equality_value | OPEN |  |  |
| TX1:241 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::initial_variant_selectors | OPEN |  |  |
| TX1:242 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::left_digest_packed_selector_tensor | OPEN |  |  |
| TX1:243 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 | OPEN |  |  |
| TX1:244 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::occupancy_lanes_factored | OPEN |  |  |
| TX1:245 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_carry_packed_selector_tensor | OPEN |  |  |
| TX1:246 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_recipient_packed_selector_tensor | OPEN |  |  |
| TX1:247 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::path_lanes_factored | OPEN |  |  |
| TX1:248 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::poseidon_selectors | OPEN |  |  |
| TX1:249 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::private_public | OPEN |  |  |
| TX1:250 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed | OPEN |  |  |
| TX1:251 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed_selector_tensor | OPEN |  |  |
| TX1:252 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::fields | OPEN |  |  |
| TX1:253 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::frontier | OPEN |  |  |
| TX1:254 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes | OPEN |  |  |
| TX1:255 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::semantic | OPEN |  |  |
| TX1:256 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::terminal_qm31 | OPEN |  |  |
| TX1:257 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::reconstruct_10 | OPEN |  |  |
| TX1:258 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::scalar_lanes | OPEN |  |  |
| TX1:259 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::selected_claim | OPEN |  |  |
| TX1:260 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_initial_and_absorption | OPEN |  |  |
| TX1:261 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_packed | OPEN |  |  |
| TX1:262 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high | OPEN |  |  |
| TX1:263 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::terminal_parts | OPEN |  |  |
| TX1:264 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::validate_transition | OPEN |  |  |
| TX1:265 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::variant_expected_output | OPEN |  |  |
| TX1:266 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::withdrawal_public | OPEN |  |  |
| TX1:267 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common | CLOSED |  |  |
| TX1:268 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public | OPEN |  |  |
| TX1:269 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_lane_transition_boxed_v1 | CLOSED |  |  |
| TX1:270 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_statement_v1 | CLOSED |  |  |
| TX1:271 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_terminal_common_boxed_v1 | CLOSED |  |  |
| TX1:272 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_transfer_statement_boxed_v1 | CLOSED |  |  |
| TX1:273 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_withdrawal_statement_boxed_v1 | CLOSED |  |  |
| TX1:274 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::statement_public_common | CLOSED |  |  |
| TX1:275 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind | CLOSED |  |  |
| TX1:276 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 | CLOSED |  |  |
| TX1:277 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1 | CLOSED |  |  |
| TX1:278 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 | CLOSED |  |  |
| TX1:279 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact | CLOSED |  |  |
| TX1:280 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate | CLOSED |  |  |
| TX1:281 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_afterstate_boxed_v1 | CLOSED |  |  |
| TX1:282 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_live_snapshot_boxed_v1 | CLOSED |  |  |
| TX1:283 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_late_public_statement_boxed_v1 | CLOSED |  |  |
| TX1:284 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_live_snapshot_v1 | CLOSED |  |  |
| TX1:285 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical | CLOSED |  |  |
| TX1:286 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1 | CLOSED |  |  |
| TX1:287 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1 | CLOSED |  |  |
| TX1:288 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1 | CLOSED |  |  |
| TX1:289 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common | CLOSED |  |  |
| TX1:290 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1 | CLOSED |  |  |
| TX1:291 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1 | CLOSED |  |  |
| TX1:292 | crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical | CLOSED |  |  |
| TX1:293 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common | CLOSED |  |  |
| TX1:294 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1 | CLOSED |  |  |
| TX1:295 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1 | CLOSED |  |  |
| TX1:296 | crates/aspis-statement/src/pool_v1/payment_relation.rs::require_header | CLOSED |  |  |
| TX1:297 | crates/aspis-statement/src/pool_v1/payment_relation.rs::transfer_common | CLOSED |  |  |
| TX1:298 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common | CLOSED |  |  |
| TX1:299 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1 | CLOSED |  |  |
| TX1:300 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1 | CLOSED |  |  |
| TX1:301 | crates/aspis-statement/src/pool_v1/payment_relation.rs::withdrawal_common | CLOSED |  |  |
| TX1:302 | crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy | OPEN |  |  |
| TX1:303 | crates/aspis-statement/src/poseidon2.rs::external_linear_lazy | OPEN |  |  |
| TX1:304 | crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy | OPEN |  |  |
| TX1:305 | crates/aspis-statement/src/poseidon2.rs::merkle_node_compress_v3 | OPEN |  |  |
| TX1:306 | crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace | OPEN |  |  |
| TX1:307 | crates/aspis-statement/src/poseidon2.rs::pow5 | OPEN |  |  |
| TX1:308 | crates/aspis-statement/src/state_only_poseidon.rs::evaluate_state_only_poseidon_oracle_projected | OPEN |  |  |
| TX1:309 | crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs | OPEN |  |  |
| TX1:310 | crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs | OPEN |  |  |
| TX1:311 | crates/aspis-statement/src/state_only_poseidon.rs::external_linear_lazy | OPEN |  |  |
| TX1:312 | crates/aspis-statement/src/state_only_poseidon.rs::external_linear_packed | OPEN |  |  |
| TX1:313 | crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed | OPEN |  |  |
| TX1:314 | crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw | OPEN |  |  |
| TX1:315 | crates/aspis-statement/src/state_only_poseidon.rs::full_round | OPEN |  |  |
| TX1:316 | crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants | OPEN |  |  |
| TX1:317 | crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants_packed | OPEN |  |  |
| TX1:318 | crates/aspis-statement/src/state_only_poseidon.rs::full_round_packed | OPEN |  |  |
| TX1:319 | crates/aspis-statement/src/state_only_poseidon.rs::internal_linear_lazy | OPEN |  |  |
| TX1:320 | crates/aspis-statement/src/state_only_poseidon.rs::internal_round | OPEN |  |  |
| TX1:321 | crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_columns | OPEN |  |  |
| TX1:322 | crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_limb | OPEN |  |  |
| TX1:323 | crates/aspis-statement/src/state_only_poseidon.rs::interpolated_full_pair_packed | OPEN |  |  |
| TX1:324 | crates/aspis-statement/src/state_only_poseidon.rs::interpolated_internal_pair | OPEN |  |  |
| TX1:325 | crates/aspis-statement/src/state_only_poseidon.rs::leading_pair_packed | OPEN |  |  |
| TX1:326 | crates/aspis-statement/src/state_only_poseidon.rs::pow5 | OPEN |  |  |
| TX1:327 | programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest | OPEN |  |  |
| TX1:328 | programs/r1-cost-probe/src/lib.rs::first_decoded | OPEN |  |  |
| TX1:329 | programs/r1-cost-probe/src/lib.rs::observer | OPEN |  |  |
| TX1:330 | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction | OPEN |  |  |
| TX1:331 | programs/r1-cost-probe/src/pool_route.rs::admitted | OPEN |  |  |
| TX1:332 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box | CLOSED |  |  |
| TX1:333 | programs/r1-cost-probe/src/r1_pool_adapter.rs::process | OPEN |  |  |
| TX1:334 | programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok | OPEN |  |  |
| TX1:335 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data | OPEN |  |  |
| TX1:336 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len | OPEN |  |  |
| TX1:337 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key | OPEN |  |  |
| TX1:338 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner | OPEN |  |  |
| TX1:339 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts | OPEN |  |  |
| TX1:340 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer | OPEN |  |  |
| TX1:341 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint | OPEN |  |  |
| TX1:342 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero | OPEN |  |  |
| TX1:343 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot | OPEN |  |  |
| TX1:344 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1 | OPEN |  |  |
| TX1:345 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned | OPEN |  |  |
| TX2:001 | crates/aspis-core/src/field.rs::CM31::add | CLOSED |  |  |
| TX2:002 | crates/aspis-core/src/field.rs::CM31::double | CLOSED |  |  |
| TX2:003 | crates/aspis-core/src/field.rs::CM31::from_le_bytes | CLOSED |  |  |
| TX2:004 | crates/aspis-core/src/field.rs::CM31::mul | CLOSED |  |  |
| TX2:005 | crates/aspis-core/src/field.rs::CM31::mul_m31 | CLOSED |  |  |
| TX2:006 | crates/aspis-core/src/field.rs::CM31::new | CLOSED |  |  |
| TX2:007 | crates/aspis-core/src/field.rs::CM31::sub | CLOSED |  |  |
| TX2:008 | crates/aspis-core/src/field.rs::CM31::write_le_bytes | OPEN |  |  |
| TX2:009 | crates/aspis-core/src/field.rs::M31::add | CLOSED |  |  |
| TX2:010 | crates/aspis-core/src/field.rs::M31::double | CLOSED |  |  |
| TX2:011 | crates/aspis-core/src/field.rs::M31::from_le_bytes | CLOSED |  |  |
| TX2:012 | crates/aspis-core/src/field.rs::M31::inv | CLOSED |  |  |
| TX2:013 | crates/aspis-core/src/field.rs::M31::mul | CLOSED |  |  |
| TX2:014 | crates/aspis-core/src/field.rs::M31::reduce_u64 | CLOSED |  |  |
| TX2:015 | crates/aspis-core/src/field.rs::M31::sub | CLOSED |  |  |
| TX2:016 | crates/aspis-core/src/field.rs::M31::to_le_bytes | CLOSED |  |  |
| TX2:017 | crates/aspis-core/src/field.rs::QM31::add | CLOSED |  |  |
| TX2:018 | crates/aspis-core/src/field.rs::QM31::from_cm31 | OPEN |  |  |
| TX2:019 | crates/aspis-core/src/field.rs::QM31::from_le_bytes | CLOSED |  |  |
| TX2:020 | crates/aspis-core/src/field.rs::QM31::mul | CLOSED |  |  |
| TX2:021 | crates/aspis-core/src/field.rs::QM31::mul_m31 | CLOSED |  |  |
| TX2:022 | crates/aspis-core/src/field.rs::QM31::square | OPEN |  |  |
| TX2:023 | crates/aspis-core/src/field.rs::QM31::sub | CLOSED |  |  |
| TX2:024 | crates/aspis-core/src/field.rs::QM31::write_le_bytes | OPEN |  |  |
| TX2:025 | crates/aspis-core/src/field.rs::mul_by_r | CLOSED |  |  |
| TX2:026 | crates/aspis-core/src/field.rs::reduce_u64 | CLOSED |  |  |
| TX2:027 | crates/aspis-core/src/field.rs::square_n | CLOSED |  |  |
| TX2:028 | crates/aspis-core/src/field/wide_exact.rs::WideExact::add | CLOSED |  |  |
| TX2:029 | crates/aspis-core/src/field/wide_exact.rs::WideExact::c0 | OPEN |  |  |
| TX2:030 | crates/aspis-core/src/field/wide_exact.rs::WideExact::c1 | OPEN |  |  |
| TX2:031 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes | CLOSED |  |  |
| TX2:032 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs | CLOSED |  |  |
| TX2:033 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31 | CLOSED |  |  |
| TX2:034 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul | CLOSED |  |  |
| TX2:035 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 | CLOSED |  |  |
| TX2:036 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 | CLOSED |  |  |
| TX2:037 | crates/aspis-core/src/field/wide_exact.rs::WideExact::new | OPEN |  |  |
| TX2:038 | crates/aspis-core/src/field/wide_exact.rs::WideExact::sub | CLOSED |  |  |
| TX2:039 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes | CLOSED |  |  |
| TX2:040 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs | CLOSED |  |  |
| TX2:041 | crates/aspis-core/src/field/wide_exact.rs::canonical_qm31 | CLOSED |  |  |
| TX2:042 | crates/aspis-core/src/field/wide_exact.rs::mul_u | CLOSED |  |  |
| TX2:043 | crates/aspis-core/src/r0/domain.rs::FibreIndex::get | CLOSED |  |  |
| TX2:044 | crates/aspis-core/src/r0/domain.rs::FibreIndex::new | CLOSED |  |  |
| TX2:045 | crates/aspis-core/src/r0/heap.rs::filled | OPEN |  |  |
| TX2:046 | crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31 | OPEN |  |  |
| TX2:047 | crates/aspis-core/src/state_only_prefix.rs::r0::statement_points | OPEN |  |  |
| TX2:048 | crates/aspis-core/src/state_only_prefix.rs::state_only_statement_points | OPEN |  |  |
| TX2:049 | crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest | OPEN |  |  |
| TX2:050 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at | OPEN |  |  |
| TX2:051 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys | OPEN |  |  |
| TX2:052 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_leaf | OPEN |  |  |
| TX2:053 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle | OPEN |  |  |
| TX2:054 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle_values | OPEN |  |  |
| TX2:055 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree | OPEN |  |  |
| TX2:056 | crates/aspis-r1-cost-probe/src/candidate.rs::opening | CLOSED |  |  |
| TX2:057 | crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape | OPEN |  |  |
| TX2:058 | crates/aspis-r1-cost-probe/src/candidate.rs::query_loop | OPEN |  |  |
| TX2:059 | crates/aspis-r1-cost-probe/src/candidate.rs::query_values | OPEN |  |  |
| TX2:060 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index | OPEN |  |  |
| TX2:061 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf | OPEN |  |  |
| TX2:062 | crates/aspis-r1-cost-probe/src/candidate.rs::slot | OPEN |  |  |
| TX2:063 | crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys | OPEN |  |  |
| TX2:064 | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated | OPEN |  |  |
| TX2:065 | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common | OPEN |  |  |
| TX2:066 | crates/aspis-r1-cost-probe/src/compact.rs::slot_offset | OPEN |  |  |
| TX2:067 | crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point | CLOSED |  |  |
| TX2:068 | crates/aspis-r1-cost-probe/src/fast_domain.rs::line_node | CLOSED |  |  |
| TX2:069 | crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value | CLOSED |  |  |
| TX2:070 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots | OPEN |  |  |
| TX2:071 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one | OPEN |  |  |
| TX2:072 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish | CLOSED |  |  |
| TX2:073 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new | CLOSED |  |  |
| TX2:074 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push | OPEN |  |  |
| TX2:075 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::finish | CLOSED |  |  |
| TX2:076 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new | CLOSED |  |  |
| TX2:077 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push | OPEN |  |  |
| TX2:078 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_limbs | CLOSED |  |  |
| TX2:079 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_wide | CLOSED |  |  |
| TX2:080 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::limbs | CLOSED |  |  |
| TX2:081 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::reduce | CLOSED |  |  |
| TX2:082 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::checked_q | CLOSED |  |  |
| TX2:083 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::limbs_of | CLOSED |  |  |
| TX2:084 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits | OPEN |  |  |
| TX2:085 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels | OPEN |  |  |
| TX2:086 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width | OPEN |  |  |
| TX2:087 | crates/aspis-r1-cost-probe/src/multiproof.rs::index_at | OPEN |  |  |
| TX2:088 | crates/aspis-r1-cost-probe/src/multiproof.rs::node_count | OPEN |  |  |
| TX2:089 | crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent | OPEN |  |  |
| TX2:090 | crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches | OPEN |  |  |
| TX2:091 | crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent | OPEN |  |  |
| TX2:092 | crates/aspis-r1-cost-probe/src/multiproof.rs::value_at | OPEN |  |  |
| TX2:093 | crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place | OPEN |  |  |
| TX2:094 | crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed | OPEN |  |  |
| TX2:095 | crates/aspis-r1-cost-probe/src/trace.rs::value | CLOSED |  |  |
| TX2:096 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len | OPEN |  |  |
| TX2:097 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::folds | OPEN |  |  |
| TX2:098 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag | CLOSED |  |  |
| TX2:099 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish | OPEN |  |  |
| TX2:100 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new | OPEN |  |  |
| TX2:101 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::push | CLOSED |  |  |
| TX2:102 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value | OPEN |  |  |
| TX2:103 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query | CLOSED |  |  |
| TX2:104 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range | QUALIFIED |  | Source-validator CLOSED; headline import duplicates verifier.Phase (NFF_FINDINGS.md L032); coherent retarget replay not in this pinned refresh |
| TX2:105 | crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::e | OPEN |  |  |
| TX2:106 | crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::k | OPEN |  |  |
| TX2:107 | crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::raw | OPEN |  |  |
| TX2:108 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node | CLOSED |  |  |
| TX2:109 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulated_weight_at | CLOSED |  |  |
| TX2:110 | crates/aspis-r1-cost-probe/src/verifier.rs::basis_at | CLOSED |  |  |
| TX2:111 | crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products | CLOSED |  |  |
| TX2:112 | crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size | OPEN |  |  |
| TX2:113 | crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses | CLOSED |  |  |
| TX2:114 | crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot | OPEN |  |  |
| TX2:115 | crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation | OPEN |  |  |
| TX2:116 | crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation_round | OPEN |  |  |
| TX2:117 | crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses | CLOSED |  |  |
| TX2:118 | crates/aspis-r1-cost-probe/src/verifier.rs::mark | CLOSED |  |  |
| TX2:119 | crates/aspis-r1-cost-probe/src/verifier.rs::polynomial | OPEN |  |  |
| TX2:120 | crates/aspis-r1-cost-probe/src/verifier.rs::power_limb_at | CLOSED |  |  |
| TX2:121 | crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_semantic_alpha | OPEN |  |  |
| TX2:122 | crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_weights | OPEN |  |  |
| TX2:123 | crates/aspis-r1-cost-probe/src/verifier.rs::residue_limb_at | CLOSED |  |  |
| TX2:124 | crates/aspis-r1-cost-probe/src/verifier.rs::resume | OPEN |  |  |
| TX2:125 | crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row | CLOSED |  |  |
| TX2:126 | crates/aspis-r1-cost-probe/src/verifier.rs::validate_checkpoint_queries | OPEN |  |  |
| TX2:127 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts | OPEN |  |  |
| TX2:128 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::new | OPEN |  |  |
| TX2:129 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::pair | OPEN |  |  |
| TX2:130 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor | OPEN |  |  |
| TX2:131 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor | OPEN |  |  |
| TX2:132 | crates/aspis-r1-cost-probe/src/weights.rs::double | OPEN |  |  |
| TX2:133 | crates/aspis-r1-cost-probe/src/weights.rs::factored_s2_libra_weights | OPEN |  |  |
| TX2:134 | crates/aspis-r1-cost-probe/src/weights.rs::field | CLOSED |  |  |
| TX2:135 | crates/aspis-r1-cost-probe/src/weights.rs::grouped_inactive_pair | OPEN |  |  |
| TX2:136 | crates/aspis-r1-cost-probe/src/weights.rs::high_dot | OPEN |  |  |
| TX2:137 | crates/aspis-r1-cost-probe/src/weights.rs::partial_dot | OPEN |  |  |
| TX2:138 | crates/aspis-r1-cost-probe/src/weights.rs::powers | OPEN |  |  |
| TX2:139 | crates/aspis-r1-cost-probe/src/weights.rs::process_kind | OPEN |  |  |
| TX2:140 | crates/aspis-r1-cost-probe/src/weights.rs::process_regular_kinds | OPEN |  |  |
| TX2:141 | crates/aspis-r1-cost-probe/src/weights.rs::push_byte_products | OPEN |  |  |
| TX2:142 | crates/aspis-r1-cost-probe/src/weights.rs::s2_grouped_inactive_pair | OPEN |  |  |
| TX2:143 | crates/aspis-r1-cost-probe/src/weights.rs::shared_high | OPEN |  |  |
| TX2:144 | crates/aspis-r1-cost-probe/src/weights.rs::shared_partials | OPEN |  |  |
| TX2:145 | crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard | OPEN |  |  |
| TX2:146 | crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical | CLOSED |  |  |
| TX2:147 | crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical | CLOSED |  |  |
| TX2:148 | crates/aspis-statement/src/atomic_statement.rs::unwrap_fixed_slice | CLOSED |  |  |
| TX2:149 | crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1 | OPEN |  |  |
| TX2:150 | crates/aspis-statement/src/pool_v1/format.rs::decode_verifier_policy_v1 | OPEN |  |  |
| TX2:151 | crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1 | OPEN |  |  |
| TX2:152 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1 | OPEN |  |  |
| TX2:153 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1 | OPEN |  |  |
| TX2:154 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical | CLOSED |  |  |
| TX2:155 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte | CLOSED |  |  |
| TX2:156 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 | CLOSED |  |  |
| TX2:157 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::validate_master | OPEN |  |  |
| TX2:158 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier | CLOSED |  |  |
| TX2:159 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind | CLOSED |  |  |
| TX2:160 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common | CLOSED |  |  |
| TX2:161 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier | CLOSED |  |  |
| TX2:162 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::transition_kind | CLOSED |  |  |
| TX2:163 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1 | CLOSED |  |  |
| TX2:164 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1 | CLOSED |  |  |
| TX2:165 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1 | CLOSED |  |  |
| TX2:166 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::statement_public_common | CLOSED |  |  |
| TX2:167 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind | CLOSED |  |  |
| TX2:168 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1 | CLOSED |  |  |
| TX2:169 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 | CLOSED |  |  |
| TX2:170 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_result | CLOSED |  |  |
| TX2:171 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1 | CLOSED |  |  |
| TX2:172 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 | CLOSED |  |  |
| TX2:173 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact | CLOSED |  |  |
| TX2:174 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate | CLOSED |  |  |
| TX2:175 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical | CLOSED |  |  |
| TX2:176 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1 | CLOSED |  |  |
| TX2:177 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1 | CLOSED |  |  |
| TX2:178 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1 | CLOSED |  |  |
| TX2:179 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common | CLOSED |  |  |
| TX2:180 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1 | CLOSED |  |  |
| TX2:181 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1 | CLOSED |  |  |
| TX2:182 | crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical | CLOSED |  |  |
| TX2:183 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common | CLOSED |  |  |
| TX2:184 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1 | CLOSED |  |  |
| TX2:185 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1 | CLOSED |  |  |
| TX2:186 | crates/aspis-statement/src/pool_v1/payment_relation.rs::require_header | CLOSED |  |  |
| TX2:187 | crates/aspis-statement/src/pool_v1/payment_relation.rs::transfer_common | CLOSED |  |  |
| TX2:188 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common | CLOSED |  |  |
| TX2:189 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1 | CLOSED |  |  |
| TX2:190 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1 | CLOSED |  |  |
| TX2:191 | crates/aspis-statement/src/pool_v1/payment_relation.rs::withdrawal_common | CLOSED |  |  |
| TX2:192 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from | OPEN |  |  |
| TX2:193 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot | OPEN |  |  |
| TX2:194 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at | OPEN |  |  |
| TX2:195 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot | OPEN |  |  |
| TX2:196 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at | OPEN |  |  |
| TX2:197 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable | OPEN |  |  |
| TX2:198 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused | OPEN |  |  |
| TX2:199 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable | OPEN |  |  |
| TX2:200 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused | OPEN |  |  |
| TX2:201 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1 | OPEN |  |  |
| TX2:202 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2 | OPEN |  |  |
| TX2:203 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1 | OPEN |  |  |
| TX2:204 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2 | OPEN |  |  |
| TX2:205 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero | OPEN |  |  |
| TX2:206 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v1 | OPEN |  |  |
| TX2:207 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v2 | OPEN |  |  |
| TX2:208 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v1 | OPEN |  |  |
| TX2:209 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v2 | OPEN |  |  |
| TX2:210 | programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest | OPEN |  |  |
| TX2:211 | programs/r1-cost-probe/src/lib.rs::error | OPEN |  |  |
| TX2:212 | programs/r1-cost-probe/src/lib.rs::observer | OPEN |  |  |
| TX2:213 | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction | OPEN |  |  |
| TX2:214 | programs/r1-cost-probe/src/pool_route.rs::admitted | OPEN |  |  |
| TX2:215 | programs/r1-cost-probe/src/r1_pool_adapter.rs::asq8_common | CLOSED |  |  |
| TX2:216 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box | OPEN |  |  |
| TX2:217 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release | OPEN |  |  |
| TX2:218 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box | OPEN |  |  |
| TX2:219 | programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result | CLOSED | RuntimeReturnData |  |
| TX2:220 | programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id | OPEN |  |  |
| TX2:221 | programs/r1-cost-probe/src/r1_pool_adapter.rs::process | OPEN |  |  |
| TX2:222 | programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok | OPEN |  |  |
| TX2:223 | programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok | OPEN |  |  |
| TX2:224 | programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement | CLOSED |  |  |
| TX2:225 | programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id | OPEN |  |  |
| TX2:226 | programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer | CLOSED | RuntimeMemcmp |  |
| TX2:227 | programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box | CLOSED |  |  |
| TX2:228 | programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box | CLOSED |  |  |
| TX2:229 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data | OPEN |  |  |
| TX2:230 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len | OPEN |  |  |
| TX2:231 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key | OPEN |  |  |
| TX2:232 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner | OPEN |  |  |
| TX2:233 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts | OPEN |  |  |
| TX2:234 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry | OPEN |  |  |
| TX2:235 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts | OPEN |  |  |
| TX2:236 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account | OPEN |  |  |
| TX2:237 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer | OPEN |  |  |
| TX2:238 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint | OPEN |  |  |
| TX2:239 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot | OPEN |  |  |
| TX2:240 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2 | OPEN |  |  |
| TX2:241 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned | OPEN |  |  |
| TX2:242 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8 | OPEN |  |  |
