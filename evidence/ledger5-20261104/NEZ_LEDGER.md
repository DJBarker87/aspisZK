# NEZ authoritative ledger

Target not yet established. Frozen source `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.

NEN history is retained. Unchanged slice validators check actual certificates, call domains, full Result/carrier/state/ordered effects, review hashes, controls, features and K-3/K-2. No Lean or Kani ran. Rulings (z)/(aa) retain existing trust; (ab) ADDS RuntimeReturnData.

| Coverage | Total | CLOSED | OPEN |
|---|---:|---:|---:|
| TX1 | 345 | 101 | 244 |
| TX2 | 242 | 101 | 141 |
| all_rows | 587 | 202 | 385 |
| unique_functions | 434 | 109 | 325 |

Contributing slice occurrences: {'Q': 120, 'S': 82}. Overlapping membership: {'Q': {'occurrences': 122, 'unique_functions': 61}, 'S': {'occurrences': 84, 'unique_functions': 50}}. Shared CLOSED occurrences: {'M31::from_le_bytes': 2, 'WideExact::to_limbs': 2}. Counted once globally. NEX reports 82 S occurrences. Unified S membership beyond NEX: {'WideExact::to_limbs': 2}.

## Roots

- Q `crates/aspis-r1-cost-probe/src/candidate.rs::query_loop`: OPEN (TX1:088, TX2:058).
- Q `crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range`: OPEN (TX1:181, TX2:104).
- S `programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box`: OPEN (TX1:332).
- S `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1`: CLOSED (TX1:276, TX2:169).
- S `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1`: CLOSED (TX2:165).
- S `programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement`: OPEN (TX2:224).
- S `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1`: OPEN (TX2:163).
- S `programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer`: OPEN (TX2:226).
- S `programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result`: OPEN (TX2:219).

Slice membership by TX: {'Q': {'TX1': 61, 'TX2': 61}, 'S': {'TX1': 42, 'TX2': 42}}.

## Slice closure reconciliation

Actual validator CLOSED counts: NEB: 66, NEE: 6, NEI: 66, NEJ: 14, NEL: 22, NEM: 50, NEN: 88, NEO: 130, NEQ: 68, NET: 144, NEU: 72, NEX: 82.

NEO/NET counts include inherited global rows; S continuations report their S rows. Full per-slice validator counts are in NEZ_validator_coverage. Rejected slice-reported CLOSED rows: 0.

## RuntimeReturnData additions and uses

RuntimeReturnData is ADDED platform trust. Pool immediate read, program-id and instruction-context association remains a separate OPEN obligation.

Model theorem uses: 5; CLOSED native occurrences: 0; CLOSED roots using (ab): 0.
- `NEX_ReturnData.set_preserves_order` → RuntimeReturnData; MODEL SUPPORT ONLY; native BindingBridge/EncoderBridge remain OPEN. Receipt `evidence/slice-s-compose8-20261104/NEX_L014/receipt.json`.
- `NEX_ReturnData.runtime_bound` → RuntimeReturnData; MODEL SUPPORT ONLY; native BindingBridge/EncoderBridge remain OPEN. Receipt `evidence/slice-s-compose8-20261104/NEX_L014/receipt.json`.
- `NEX_ReturnData.observable` → RuntimeReturnData; MODEL SUPPORT ONLY; native BindingBridge/EncoderBridge remain OPEN. Receipt `evidence/slice-s-compose8-20261104/NEX_L014/receipt.json`.
- `NEX_EmitRuntime.result_state_effects` → RuntimeReturnData; MODEL SUPPORT ONLY; native BindingBridge/EncoderBridge remain OPEN. Receipt `evidence/slice-s-compose8-20261104/NEX_L039/receipt.json`.
- `NEX_EmitRuntime.success` → RuntimeReturnData; MODEL SUPPORT ONLY; native BindingBridge/EncoderBridge remain OPEN. Receipt `evidence/slice-s-compose8-20261104/NEX_L039/receipt.json`.

## Occurrence admission and rejection reasons

| Row | Function | Composed | Provider | Trust additions | Reason |
|---|---|---|---|---|---|
| TX1:001 | crates/aspis-core/src/field.rs::CM31::add | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:002 | crates/aspis-core/src/field.rs::CM31::double | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:003 | crates/aspis-core/src/field.rs::CM31::from_le_bytes | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:004 | crates/aspis-core/src/field.rs::CM31::from_m31 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:005 | crates/aspis-core/src/field.rs::CM31::inv | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:006 | crates/aspis-core/src/field.rs::CM31::inv_with | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:007 | crates/aspis-core/src/field.rs::CM31::mul | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:008 | crates/aspis-core/src/field.rs::CM31::mul_m31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:009 | crates/aspis-core/src/field.rs::CM31::neg | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:010 | crates/aspis-core/src/field.rs::CM31::new | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:011 | crates/aspis-core/src/field.rs::CM31::square | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:012 | crates/aspis-core/src/field.rs::CM31::sub | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:013 | crates/aspis-core/src/field.rs::M31::add | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:014 | crates/aspis-core/src/field.rs::M31::double | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:015 | crates/aspis-core/src/field.rs::M31::from_le_bytes | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:016 | crates/aspis-core/src/field.rs::M31::inv | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:017 | crates/aspis-core/src/field.rs::M31::mul | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:018 | crates/aspis-core/src/field.rs::M31::neg | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:019 | crates/aspis-core/src/field.rs::M31::reduce_u62 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:020 | crates/aspis-core/src/field.rs::M31::reduce_u64 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:021 | crates/aspis-core/src/field.rs::M31::sub | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:022 | crates/aspis-core/src/field.rs::M31::to_le_bytes | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:023 | crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:024 | crates/aspis-core/src/field.rs::QM31::add | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:025 | crates/aspis-core/src/field.rs::QM31::from_cm31 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:026 | crates/aspis-core/src/field.rs::QM31::from_le_bytes | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:027 | crates/aspis-core/src/field.rs::QM31::inv | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:028 | crates/aspis-core/src/field.rs::QM31::is_zero | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:029 | crates/aspis-core/src/field.rs::QM31::mul | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:030 | crates/aspis-core/src/field.rs::QM31::mul_m31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:031 | crates/aspis-core/src/field.rs::QM31::neg | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:032 | crates/aspis-core/src/field.rs::QM31::square | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:033 | crates/aspis-core/src/field.rs::QM31::sub | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:034 | crates/aspis-core/src/field.rs::QM31::try_inv | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:035 | crates/aspis-core/src/field.rs::mul_by_r | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:036 | crates/aspis-core/src/field.rs::qm31_accumulate_product_channels | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:037 | crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:038 | crates/aspis-core/src/field.rs::qm31_m31_dot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:039 | crates/aspis-core/src/field.rs::qm31_pack_base4 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:040 | crates/aspis-core/src/field.rs::qm31_sum_products2 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:041 | crates/aspis-core/src/field.rs::qm31_sum_products3 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:042 | crates/aspis-core/src/field.rs::qm31_sum_products3_prepared | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:043 | crates/aspis-core/src/field.rs::qm31_sum_products4 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:044 | crates/aspis-core/src/field.rs::qm31_sum_products_small | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:045 | crates/aspis-core/src/field.rs::reduce_u64 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:046 | crates/aspis-core/src/field.rs::square_n | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:047 | crates/aspis-core/src/field/wide_exact.rs::WideExact::add | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:048 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:049 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:050 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:051 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:052 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:053 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:054 | crates/aspis-core/src/field/wide_exact.rs::WideExact::neg | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:055 | crates/aspis-core/src/field/wide_exact.rs::WideExact::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:056 | crates/aspis-core/src/field/wide_exact.rs::WideExact::square | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:057 | crates/aspis-core/src/field/wide_exact.rs::WideExact::sub | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:058 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:059 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:060 | crates/aspis-core/src/field/wide_exact.rs::canonical_qm31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:061 | crates/aspis-core/src/field/wide_exact.rs::mul_u | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:062 | crates/aspis-core/src/r0/domain.rs::FibreIndex::get | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:063 | crates/aspis-core/src/r0/domain.rs::FibreIndex::new | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:064 | crates/aspis-core/src/r0/heap.rs::filled | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:065 | crates/aspis-core/src/r0/merkle.rs::parent_with_digest | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:066 | crates/aspis-core/src/r0_transcript.rs::QueryScan::finish | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:067 | crates/aspis-core/src/r0_transcript.rs::QueryScan::scan | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:068 | crates/aspis-core/src/r0_transcript.rs::block_rank | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:069 | crates/aspis-core/src/r0_transcript.rs::queries_from_pairs | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:070 | crates/aspis-core/src/r0_transcript.rs::query_words | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:071 | crates/aspis-core/src/state_only_hiding.rs::cm31_mul_i | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:072 | crates/aspis-core/src/state_only_hiding.rs::cm31_mul_r | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:073 | crates/aspis-core/src/state_only_hiding.rs::mask_power_26 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:074 | crates/aspis-core/src/state_only_hiding.rs::mul_tower_basis | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:075 | crates/aspis-core/src/state_only_hiding.rs::selected_mask_linears | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:076 | crates/aspis-core/src/state_only_hiding.rs::state_only_selected_mask_value | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:077 | crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:078 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:079 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:080 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_leaf | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:081 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:082 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle_values | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:083 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:084 | crates/aspis-r1-cost-probe/src/candidate.rs::canonical_scan | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:085 | crates/aspis-r1-cost-probe/src/candidate.rs::opening | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:086 | crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:087 | crates/aspis-r1-cost-probe/src/candidate.rs::prepare | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:088 | crates/aspis-r1-cost-probe/src/candidate.rs::query_loop | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:089 | crates/aspis-r1-cost-probe/src/candidate.rs::query_values | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:090 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:091 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:092 | crates/aspis-r1-cost-probe/src/candidate.rs::slot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:093 | crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:094 | crates/aspis-r1-cost-probe/src/candidate.rs::tx1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:095 | crates/aspis-r1-cost-probe/src/candidate.rs::wide_view | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:096 | crates/aspis-r1-cost-probe/src/compact.rs::check_values | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:097 | crates/aspis-r1-cost-probe/src/compact.rs::compact_row | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:098 | crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:099 | crates/aspis-r1-cost-probe/src/compact.rs::expand_values | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:100 | crates/aspis-r1-cost-probe/src/compact.rs::slot_offset | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:101 | crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:102 | crates/aspis-r1-cost-probe/src/fast_domain.rs::line_node | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:103 | crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:104 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:105 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:106 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:107 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:108 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:109 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::finish | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:110 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:111 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:112 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_limbs | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:113 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_wide | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:114 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::limbs | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:115 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::reduce | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:116 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::checked_q | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:117 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::limbs_of | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:118 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:119 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:120 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:121 | crates/aspis-r1-cost-probe/src/multiproof.rs::index_at | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:122 | crates/aspis-r1-cost-probe/src/multiproof.rs::node_count | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:123 | crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:124 | crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:125 | crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:126 | crates/aspis-r1-cost-probe/src/multiproof.rs::value_at | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:127 | crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:128 | crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:129 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::claims | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:130 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:131 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::public_transcript | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:132 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_boundary | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:133 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_round | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:134 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_rounds | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:135 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_value | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:136 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_finish | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:137 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:138 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::parse | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:139 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::payload | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:140 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:141 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:142 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::circle_validated | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:143 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:144 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:145 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::semantic_validated | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:146 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:147 | crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:148 | crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::framed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:149 | crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:150 | crates/aspis-r1-cost-probe/src/r1_wire.rs::begin | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:151 | crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:152 | crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record_at | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:153 | crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:154 | crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:155 | crates/aspis-r1-cost-probe/src/sampler.rs::add_small_base_p | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:156 | crates/aspis-r1-cost-probe/src/sampler.rs::circle_sample | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:157 | crates/aspis-r1-cost-probe/src/sampler.rs::decode8 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:158 | crates/aspis-r1-cost-probe/src/sampler.rs::gamma_sample | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:159 | crates/aspis-r1-cost-probe/src/sampler.rs::low_base_p_digits | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:160 | crates/aspis-r1-cost-probe/src/sampler.rs::ordinary_sample | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:161 | crates/aspis-r1-cost-probe/src/sampler.rs::qm31_digits | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:162 | crates/aspis-r1-cost-probe/src/sampler.rs::qm31_div_pass | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:163 | crates/aspis-r1-cost-probe/src/sampler.rs::qm31_sample | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:164 | crates/aspis-r1-cost-probe/src/trace.rs::value | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:165 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::absorb | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:166 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::block | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:167 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:168 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:169 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:170 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar_k | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:171 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:172 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::folds | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:173 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:174 | crates/aspis-r1-cost-probe/src/verifier.rs::Accumulator::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:175 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:176 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:177 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::push | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:178 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:179 | crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:180 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:181 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:182 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:183 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulated_weight_at | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:184 | crates/aspis-r1-cost-probe/src/verifier.rs::basis_at | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:185 | crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:186 | crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:187 | crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:188 | crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:189 | crates/aspis-r1-cost-probe/src/verifier.rs::echeck | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:190 | crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:191 | crates/aspis-r1-cost-probe/src/verifier.rs::mark | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:192 | crates/aspis-r1-cost-probe/src/verifier.rs::power_limb_at | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:193 | crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:194 | crates/aspis-r1-cost-probe/src/verifier.rs::residue_limb_at | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:195 | crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:196 | crates/aspis-r1-cost-probe/src/weights.rs::field | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:197 | crates/aspis-r1-cost-probe/src/weights.rs::powers | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:198 | crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:199 | crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:200 | crates/aspis-statement/src/atomic_statement.rs::unwrap_fixed_slice | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:201 | crates/aspis-statement/src/pool_v1/format.rs::pool_v1_tree_parent | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:202 | crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::default | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:203 | crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::empty | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:204 | crates/aspis-statement/src/pool_v1/incremental_merkle.rs::pool_v1_empty_roots | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:205 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:206 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:207 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:208 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:209 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active_mask_basis | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:210 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::at_point | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:211 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::boxed_at_point | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:212 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::expand | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:213 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:214 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::accumulate_endpoint_selector_tensor_basis | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:215 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_residual | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:216 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_dot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:217 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_value | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:218 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::evaluate_with_selectors | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:219 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_pattern_basis_values | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:220 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_selector_tensor_basis | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:221 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:222 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::link_weight | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:223 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:224 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values_windowed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:225 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::qm31_sum_products_up_to4 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:226 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::selected_binary_weight | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:227 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::absorption_lanes_factored | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:228 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_occupancy_lanes | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:229 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_path_lanes | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:230 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:231 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted_shared_selector | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:232 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_schedule_lanes | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:233 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_value_lanes | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:234 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_level_packed_selector_tensor | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:235 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_levels_packed_selector_tensor | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:236 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::bounded_append_carry | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:237 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::composition_parts | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:238 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::copy_variant | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:239 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::empty_root | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:240 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::equality_value | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:241 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::initial_variant_selectors | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:242 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::left_digest_packed_selector_tensor | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:243 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:244 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::occupancy_lanes_factored | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:245 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_carry_packed_selector_tensor | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:246 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_recipient_packed_selector_tensor | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:247 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::path_lanes_factored | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:248 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::poseidon_selectors | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:249 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::private_public | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:250 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:251 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed_selector_tensor | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:252 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::fields | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:253 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::frontier | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:254 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:255 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::semantic | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:256 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::terminal_qm31 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:257 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::reconstruct_10 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:258 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::scalar_lanes | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:259 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::selected_claim | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:260 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_initial_and_absorption | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:261 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_packed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:262 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:263 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::terminal_parts | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:264 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::validate_transition | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:265 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::variant_expected_output | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:266 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::withdrawal_public | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:267 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:268 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:269 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_lane_transition_boxed_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:270 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_statement_v1 | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:271 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_terminal_common_boxed_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:272 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_transfer_statement_boxed_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:273 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_withdrawal_statement_boxed_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:274 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::statement_public_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:275 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:276 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:277 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:278 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:279 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:280 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:281 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_afterstate_boxed_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:282 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_live_snapshot_boxed_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:283 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_late_public_statement_boxed_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:284 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_live_snapshot_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:285 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:286 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:287 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:288 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:289 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:290 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:291 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:292 | crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:293 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:294 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:295 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:296 | crates/aspis-statement/src/pool_v1/payment_relation.rs::require_header | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:297 | crates/aspis-statement/src/pool_v1/payment_relation.rs::transfer_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:298 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:299 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:300 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:301 | crates/aspis-statement/src/pool_v1/payment_relation.rs::withdrawal_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX1:302 | crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:303 | crates/aspis-statement/src/poseidon2.rs::external_linear_lazy | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:304 | crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:305 | crates/aspis-statement/src/poseidon2.rs::merkle_node_compress_v3 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:306 | crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:307 | crates/aspis-statement/src/poseidon2.rs::pow5 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:308 | crates/aspis-statement/src/state_only_poseidon.rs::evaluate_state_only_poseidon_oracle_projected | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:309 | crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:310 | crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:311 | crates/aspis-statement/src/state_only_poseidon.rs::external_linear_lazy | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:312 | crates/aspis-statement/src/state_only_poseidon.rs::external_linear_packed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:313 | crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:314 | crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:315 | crates/aspis-statement/src/state_only_poseidon.rs::full_round | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:316 | crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:317 | crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants_packed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:318 | crates/aspis-statement/src/state_only_poseidon.rs::full_round_packed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:319 | crates/aspis-statement/src/state_only_poseidon.rs::internal_linear_lazy | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:320 | crates/aspis-statement/src/state_only_poseidon.rs::internal_round | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:321 | crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_columns | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:322 | crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_limb | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:323 | crates/aspis-statement/src/state_only_poseidon.rs::interpolated_full_pair_packed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:324 | crates/aspis-statement/src/state_only_poseidon.rs::interpolated_internal_pair | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:325 | crates/aspis-statement/src/state_only_poseidon.rs::leading_pair_packed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:326 | crates/aspis-statement/src/state_only_poseidon.rs::pow5 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:327 | programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:328 | programs/r1-cost-probe/src/lib.rs::first_decoded | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:329 | programs/r1-cost-probe/src/lib.rs::observer | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:330 | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:331 | programs/r1-cost-probe/src/pool_route.rs::admitted | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:332 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:333 | programs/r1-cost-probe/src/r1_pool_adapter.rs::process | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:334 | programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:335 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:336 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:337 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:338 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:339 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:340 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:341 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:342 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:343 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:344 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX1:345 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:001 | crates/aspis-core/src/field.rs::CM31::add | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:002 | crates/aspis-core/src/field.rs::CM31::double | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:003 | crates/aspis-core/src/field.rs::CM31::from_le_bytes | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:004 | crates/aspis-core/src/field.rs::CM31::mul | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:005 | crates/aspis-core/src/field.rs::CM31::mul_m31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:006 | crates/aspis-core/src/field.rs::CM31::new | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:007 | crates/aspis-core/src/field.rs::CM31::sub | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:008 | crates/aspis-core/src/field.rs::CM31::write_le_bytes | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:009 | crates/aspis-core/src/field.rs::M31::add | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:010 | crates/aspis-core/src/field.rs::M31::double | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:011 | crates/aspis-core/src/field.rs::M31::from_le_bytes | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:012 | crates/aspis-core/src/field.rs::M31::inv | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:013 | crates/aspis-core/src/field.rs::M31::mul | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:014 | crates/aspis-core/src/field.rs::M31::reduce_u64 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:015 | crates/aspis-core/src/field.rs::M31::sub | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:016 | crates/aspis-core/src/field.rs::M31::to_le_bytes | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:017 | crates/aspis-core/src/field.rs::QM31::add | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:018 | crates/aspis-core/src/field.rs::QM31::from_cm31 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:019 | crates/aspis-core/src/field.rs::QM31::from_le_bytes | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:020 | crates/aspis-core/src/field.rs::QM31::mul | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:021 | crates/aspis-core/src/field.rs::QM31::mul_m31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:022 | crates/aspis-core/src/field.rs::QM31::square | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:023 | crates/aspis-core/src/field.rs::QM31::sub | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:024 | crates/aspis-core/src/field.rs::QM31::write_le_bytes | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:025 | crates/aspis-core/src/field.rs::mul_by_r | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:026 | crates/aspis-core/src/field.rs::reduce_u64 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:027 | crates/aspis-core/src/field.rs::square_n | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:028 | crates/aspis-core/src/field/wide_exact.rs::WideExact::add | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:029 | crates/aspis-core/src/field/wide_exact.rs::WideExact::c0 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:030 | crates/aspis-core/src/field/wide_exact.rs::WideExact::c1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:031 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:032 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:033 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:034 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:035 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:036 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:037 | crates/aspis-core/src/field/wide_exact.rs::WideExact::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:038 | crates/aspis-core/src/field/wide_exact.rs::WideExact::sub | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:039 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:040 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:041 | crates/aspis-core/src/field/wide_exact.rs::canonical_qm31 | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:042 | crates/aspis-core/src/field/wide_exact.rs::mul_u | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:043 | crates/aspis-core/src/r0/domain.rs::FibreIndex::get | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:044 | crates/aspis-core/src/r0/domain.rs::FibreIndex::new | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:045 | crates/aspis-core/src/r0/heap.rs::filled | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:046 | crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:047 | crates/aspis-core/src/state_only_prefix.rs::r0::statement_points | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:048 | crates/aspis-core/src/state_only_prefix.rs::state_only_statement_points | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:049 | crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:050 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:051 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:052 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_leaf | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:053 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:054 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle_values | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:055 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:056 | crates/aspis-r1-cost-probe/src/candidate.rs::opening | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:057 | crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:058 | crates/aspis-r1-cost-probe/src/candidate.rs::query_loop | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:059 | crates/aspis-r1-cost-probe/src/candidate.rs::query_values | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:060 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:061 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:062 | crates/aspis-r1-cost-probe/src/candidate.rs::slot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:063 | crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:064 | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:065 | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:066 | crates/aspis-r1-cost-probe/src/compact.rs::slot_offset | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:067 | crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:068 | crates/aspis-r1-cost-probe/src/fast_domain.rs::line_node | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:069 | crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:070 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:071 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:072 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:073 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:074 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:075 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::finish | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:076 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:077 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:078 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_limbs | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:079 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_wide | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:080 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::limbs | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:081 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::reduce | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:082 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::checked_q | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:083 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::limbs_of | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:084 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:085 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:086 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:087 | crates/aspis-r1-cost-probe/src/multiproof.rs::index_at | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:088 | crates/aspis-r1-cost-probe/src/multiproof.rs::node_count | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:089 | crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:090 | crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:091 | crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:092 | crates/aspis-r1-cost-probe/src/multiproof.rs::value_at | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:093 | crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:094 | crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:095 | crates/aspis-r1-cost-probe/src/trace.rs::value | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:096 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:097 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::folds | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:098 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:099 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:100 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:101 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::push | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:102 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:103 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:104 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:105 | crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::e | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:106 | crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::k | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:107 | crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::raw | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:108 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node | OPEN | Q |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:109 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulated_weight_at | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:110 | crates/aspis-r1-cost-probe/src/verifier.rs::basis_at | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:111 | crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:112 | crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:113 | crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:114 | crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:115 | crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:116 | crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation_round | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:117 | crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:118 | crates/aspis-r1-cost-probe/src/verifier.rs::mark | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:119 | crates/aspis-r1-cost-probe/src/verifier.rs::polynomial | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:120 | crates/aspis-r1-cost-probe/src/verifier.rs::power_limb_at | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:121 | crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_semantic_alpha | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:122 | crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_weights | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:123 | crates/aspis-r1-cost-probe/src/verifier.rs::residue_limb_at | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:124 | crates/aspis-r1-cost-probe/src/verifier.rs::resume | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:125 | crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:126 | crates/aspis-r1-cost-probe/src/verifier.rs::validate_checkpoint_queries | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:127 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:128 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::new | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:129 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::pair | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:130 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:131 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:132 | crates/aspis-r1-cost-probe/src/weights.rs::double | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:133 | crates/aspis-r1-cost-probe/src/weights.rs::factored_s2_libra_weights | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:134 | crates/aspis-r1-cost-probe/src/weights.rs::field | CLOSED | Q |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:135 | crates/aspis-r1-cost-probe/src/weights.rs::grouped_inactive_pair | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:136 | crates/aspis-r1-cost-probe/src/weights.rs::high_dot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:137 | crates/aspis-r1-cost-probe/src/weights.rs::partial_dot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:138 | crates/aspis-r1-cost-probe/src/weights.rs::powers | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:139 | crates/aspis-r1-cost-probe/src/weights.rs::process_kind | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:140 | crates/aspis-r1-cost-probe/src/weights.rs::process_regular_kinds | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:141 | crates/aspis-r1-cost-probe/src/weights.rs::push_byte_products | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:142 | crates/aspis-r1-cost-probe/src/weights.rs::s2_grouped_inactive_pair | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:143 | crates/aspis-r1-cost-probe/src/weights.rs::shared_high | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:144 | crates/aspis-r1-cost-probe/src/weights.rs::shared_partials | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:145 | crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:146 | crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:147 | crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:148 | crates/aspis-statement/src/atomic_statement.rs::unwrap_fixed_slice | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:149 | crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:150 | crates/aspis-statement/src/pool_v1/format.rs::decode_verifier_policy_v1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:151 | crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:152 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:153 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:154 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:155 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:156 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:157 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::validate_master | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:158 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:159 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:160 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:161 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:162 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::transition_kind | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:163 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1 | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:164 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1 | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:165 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:166 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::statement_public_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:167 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:168 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1 | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:169 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:170 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_result | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:171 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:172 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:173 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:174 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:175 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:176 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:177 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:178 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:179 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:180 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:181 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:182 | crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:183 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:184 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:185 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:186 | crates/aspis-statement/src/pool_v1/payment_relation.rs::require_header | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:187 | crates/aspis-statement/src/pool_v1/payment_relation.rs::transfer_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:188 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:189 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:190 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1 | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:191 | crates/aspis-statement/src/pool_v1/payment_relation.rs::withdrawal_common | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:192 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:193 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:194 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:195 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:196 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:197 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:198 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:199 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:200 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:201 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:202 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:203 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:204 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:205 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:206 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:207 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v2 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:208 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v1 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:209 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v2 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:210 | programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:211 | programs/r1-cost-probe/src/lib.rs::error | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:212 | programs/r1-cost-probe/src/lib.rs::observer | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:213 | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:214 | programs/r1-cost-probe/src/pool_route.rs::admitted | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:215 | programs/r1-cost-probe/src/r1_pool_adapter.rs::asq8_common | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:216 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:217 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:218 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:219 | programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result | OPEN | S | RuntimeReturnData | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:220 | programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:221 | programs/r1-cost-probe/src/r1_pool_adapter.rs::process | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:222 | programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:223 | programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:224 | programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:225 | programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:226 | programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer | OPEN | S |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:227 | programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:228 | programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box | CLOSED | S |  | All unchanged certificate gates plus unified denial gates accepted |
| TX2:229 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:230 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:231 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:232 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:233 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:234 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:235 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:236 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:237 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:238 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:239 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:240 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:241 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
| TX2:242 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8 | OPEN |  |  | Missing complete row/call-domain/hypothesis composition certificate |
