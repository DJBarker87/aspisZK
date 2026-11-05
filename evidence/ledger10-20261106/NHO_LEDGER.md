# Ledger refresh 10

Target not yet established. CLOSED means conditional hybrid composition under retained trust.

| Scope | Total | CLOSED | QUALIFIED | OPEN |
|---|---:|---:|---:|---:|
| all | 599 | 335 | 0 | 264 |
| TX1 | 353 | 182 | 0 | 171 |
| TX2 | 246 | 153 | 0 | 93 |
| S | 97 | 97 | 0 | 0 |
| Q | 161 | 159 | 0 | 2 |
| D | 345 | 83 | 0 | 262 |

The supplied deltas reproduce 335/599 CLOSED, ten above the approximate request estimate. 34 claimed occurrences minus two already CLOSED NGX overlaps produce32 new rows. NHO_COUNT_RECONCILIATION.json retains exact membership; no graph or source change. NGW credit requires NHE_L001 scanner rerun exit0.

Routes are explicit per row: (y), (ad), (ae), (ah), (ai), (al), and reclassification. Pool A uses (af), outside599. NHH CM31::inv is a fixed M31::inv specialization; generic CM31::inv_with remains OPEN under the K-2 quarantine. TOOL-BOUNDARY TX1:036/040/041/043/044 remain OPEN.

RuntimeClockSlotBinding and ReviewedTranscription-prepared_claim are ADDED-LEAD, the latter used by TX1:193 under (ah). RuntimeCpiReadonlyEntry7 is ADDED-PENDING-LEAD and UNUSED. RuntimeReturnData (nonempty1..1024) and RuntimeMemcmp remain ACCEPTED. P6/D188 option A is reclassification, never removal. L154 is a statement parameter; coherent digest/error op43/op44.

## Pool consumer rows (outside599)

| Row | Status | Route |
|---|---|---|
| Pool meta association A | CLOSED by reclassification | (af) |
| POOL.prefix_to_cpi::pair_forest_dispatch.supported_loader | CLOSED | (y) |
| POOL.prefix_to_cpi (B) | OPEN | native production association |
| POOL.read_to_settlement (D) | OPEN | same-CPI settlement |

## TOOL-BOUNDARY rows

| Row | Function | Status |
|---|---|---|
| TX1:036 | crates/aspis-core/src/field.rs::qm31_accumulate_product_channels | OPEN |
| TX1:040 | crates/aspis-core/src/field.rs::qm31_sum_products2 | OPEN |
| TX1:041 | crates/aspis-core/src/field.rs::qm31_sum_products3 | OPEN |
| TX1:043 | crates/aspis-core/src/field.rs::qm31_sum_products4 | OPEN |
| TX1:044 | crates/aspis-core/src/field.rs::qm31_sum_products_small | OPEN |

## Verifier inventory

| Row | Function | Status | Route/boundary | Provider |
|---|---|---|---|---|
| TX1:001 | crates/aspis-core/src/field.rs::CM31::add | CLOSED | (y) plain | Q |
| TX1:002 | crates/aspis-core/src/field.rs::CM31::double | CLOSED | (y) plain | Q |
| TX1:003 | crates/aspis-core/src/field.rs::CM31::from_le_bytes | CLOSED | (y) plain | Q |
| TX1:004 | crates/aspis-core/src/field.rs::CM31::from_m31 | CLOSED | (y) plain | NFQ |
| TX1:005 | crates/aspis-core/src/field.rs::CM31::inv | CLOSED | (y)/(al) | NHH |
| TX1:006 | crates/aspis-core/src/field.rs::CM31::inv_with | OPEN |  | Q |
| TX1:007 | crates/aspis-core/src/field.rs::CM31::mul | CLOSED | (y) plain | Q |
| TX1:008 | crates/aspis-core/src/field.rs::CM31::mul_m31 | CLOSED | (y) plain | Q |
| TX1:009 | crates/aspis-core/src/field.rs::CM31::neg | CLOSED | (y) plain | NFG |
| TX1:010 | crates/aspis-core/src/field.rs::CM31::new | CLOSED | (y) plain | Q |
| TX1:011 | crates/aspis-core/src/field.rs::CM31::square | CLOSED | (y) | NFT |
| TX1:012 | crates/aspis-core/src/field.rs::CM31::sub | CLOSED | (y) plain | Q |
| TX1:013 | crates/aspis-core/src/field.rs::M31::add | CLOSED | (y) plain | Q |
| TX1:014 | crates/aspis-core/src/field.rs::M31::double | CLOSED | (y) plain | Q |
| TX1:015 | crates/aspis-core/src/field.rs::M31::from_le_bytes | CLOSED | (y) plain | S |
| TX1:016 | crates/aspis-core/src/field.rs::M31::inv | CLOSED | (y) plain | NEW |
| TX1:017 | crates/aspis-core/src/field.rs::M31::mul | CLOSED | (y) plain | Q |
| TX1:018 | crates/aspis-core/src/field.rs::M31::neg | CLOSED | (y) plain | NFQ |
| TX1:019 | crates/aspis-core/src/field.rs::M31::reduce_u62 | CLOSED | (y) plain | NFQ |
| TX1:020 | crates/aspis-core/src/field.rs::M31::reduce_u64 | CLOSED | (y) plain | Q |
| TX1:021 | crates/aspis-core/src/field.rs::M31::sub | CLOSED | (y) plain | Q |
| TX1:022 | crates/aspis-core/src/field.rs::M31::to_le_bytes | CLOSED | (y) plain | NFY |
| TX1:023 | crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new | CLOSED | (y) plain | NFQ |
| TX1:024 | crates/aspis-core/src/field.rs::QM31::add | CLOSED | (y) plain | Q |
| TX1:025 | crates/aspis-core/src/field.rs::QM31::from_cm31 | CLOSED | (y) plain | NFQ |
| TX1:026 | crates/aspis-core/src/field.rs::QM31::from_le_bytes | CLOSED | (y) plain | Q |
| TX1:027 | crates/aspis-core/src/field.rs::QM31::inv | CLOSED | (y) | NHH |
| TX1:028 | crates/aspis-core/src/field.rs::QM31::is_zero | CLOSED | (y) plain | NFG |
| TX1:029 | crates/aspis-core/src/field.rs::QM31::mul | CLOSED | (y) plain | Q |
| TX1:030 | crates/aspis-core/src/field.rs::QM31::mul_m31 | CLOSED | (y) plain | Q |
| TX1:031 | crates/aspis-core/src/field.rs::QM31::neg | OPEN |  | Q |
| TX1:032 | crates/aspis-core/src/field.rs::QM31::square | CLOSED | (y) | NGH |
| TX1:033 | crates/aspis-core/src/field.rs::QM31::sub | CLOSED | (y) plain | Q |
| TX1:034 | crates/aspis-core/src/field.rs::QM31::try_inv | CLOSED | (y) | NHH |
| TX1:035 | crates/aspis-core/src/field.rs::mul_by_r | CLOSED | (y) plain | Q |
| TX1:036 | crates/aspis-core/src/field.rs::qm31_accumulate_product_channels | OPEN | TOOL-BOUNDARY | inherited |
| TX1:037 | crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums | CLOSED | (y) | NFT |
| TX1:038 | crates/aspis-core/src/field.rs::qm31_m31_dot | CLOSED | (y) | NFT |
| TX1:039 | crates/aspis-core/src/field.rs::qm31_pack_base4 | CLOSED | (y) | NFT |
| TX1:040 | crates/aspis-core/src/field.rs::qm31_sum_products2 | OPEN | TOOL-BOUNDARY | inherited |
| TX1:041 | crates/aspis-core/src/field.rs::qm31_sum_products3 | OPEN | TOOL-BOUNDARY | inherited |
| TX1:042 | crates/aspis-core/src/field.rs::qm31_sum_products3_prepared | CLOSED | (y) | NFT |
| TX1:043 | crates/aspis-core/src/field.rs::qm31_sum_products4 | OPEN | TOOL-BOUNDARY | inherited |
| TX1:044 | crates/aspis-core/src/field.rs::qm31_sum_products_small | OPEN | TOOL-BOUNDARY | inherited |
| TX1:045 | crates/aspis-core/src/field.rs::reduce_u64 | CLOSED | (y) plain | Q |
| TX1:046 | crates/aspis-core/src/field.rs::square_n | CLOSED | (y) plain | Q |
| TX1:047 | crates/aspis-core/src/field/wide_exact.rs::WideExact::add | CLOSED | (y) plain | Q |
| TX1:048 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes | CLOSED | (y) plain | Q |
| TX1:049 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs | CLOSED | (y) plain | Q |
| TX1:050 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31 | CLOSED | (y) plain | Q |
| TX1:051 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul | CLOSED | (y) plain | Q |
| TX1:052 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 | CLOSED | (y) plain | Q |
| TX1:053 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 | CLOSED | (y) plain | Q |
| TX1:054 | crates/aspis-core/src/field/wide_exact.rs::WideExact::neg | CLOSED | (y) | NFT |
| TX1:055 | crates/aspis-core/src/field/wide_exact.rs::WideExact::new | CLOSED | (y) | NFT |
| TX1:056 | crates/aspis-core/src/field/wide_exact.rs::WideExact::square | CLOSED | (y) | NGH |
| TX1:057 | crates/aspis-core/src/field/wide_exact.rs::WideExact::sub | CLOSED | (y) plain | Q |
| TX1:058 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes | CLOSED | (y) plain | NFY |
| TX1:059 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs | CLOSED | (y) plain | Q |
| TX1:060 | crates/aspis-core/src/field/wide_exact.rs::canonical_qm31 | CLOSED | (y) plain | Q |
| TX1:061 | crates/aspis-core/src/field/wide_exact.rs::mul_u | CLOSED | (y) plain | Q |
| TX1:062 | crates/aspis-core/src/r0/domain.rs::FibreIndex::get | CLOSED | (y) plain | Q |
| TX1:063 | crates/aspis-core/src/r0/domain.rs::FibreIndex::new | CLOSED | (y) plain | Q |
| TX1:064 | crates/aspis-core/src/r0/heap.rs::filled | CLOSED | (y) | NGC |
| TX1:065 | crates/aspis-core/src/r0/merkle.rs::parent_with_digest | OPEN |  | inherited |
| TX1:066 | crates/aspis-core/src/r0_transcript.rs::QueryScan::finish | OPEN |  | inherited |
| TX1:067 | crates/aspis-core/src/r0_transcript.rs::QueryScan::scan | OPEN |  | inherited |
| TX1:068 | crates/aspis-core/src/r0_transcript.rs::block_rank | OPEN |  | inherited |
| TX1:069 | crates/aspis-core/src/r0_transcript.rs::queries_from_pairs | OPEN |  | inherited |
| TX1:070 | crates/aspis-core/src/r0_transcript.rs::query_words | OPEN |  | inherited |
| TX1:071 | crates/aspis-core/src/state_only_hiding.rs::cm31_mul_i | OPEN |  | inherited |
| TX1:072 | crates/aspis-core/src/state_only_hiding.rs::cm31_mul_r | CLOSED | (y) | NFT |
| TX1:073 | crates/aspis-core/src/state_only_hiding.rs::mask_power_26 | OPEN |  | inherited |
| TX1:074 | crates/aspis-core/src/state_only_hiding.rs::mul_tower_basis | OPEN |  | inherited |
| TX1:075 | crates/aspis-core/src/state_only_hiding.rs::selected_mask_linears | OPEN |  | inherited |
| TX1:076 | crates/aspis-core/src/state_only_hiding.rs::state_only_selected_mask_value | OPEN |  | inherited |
| TX1:077 | crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest | OPEN |  | inherited |
| TX1:078 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at | OPEN |  | inherited |
| TX1:079 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys | OPEN |  | inherited |
| TX1:080 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_leaf | OPEN |  | inherited |
| TX1:081 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle | OPEN |  | inherited |
| TX1:082 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle_values | OPEN |  | inherited |
| TX1:083 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree | OPEN |  | inherited |
| TX1:084 | crates/aspis-r1-cost-probe/src/candidate.rs::canonical_scan | OPEN |  | inherited |
| TX1:085 | crates/aspis-r1-cost-probe/src/candidate.rs::opening | CLOSED | (y) plain | Q |
| TX1:086 | crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape | OPEN |  | inherited |
| TX1:087 | crates/aspis-r1-cost-probe/src/candidate.rs::prepare | OPEN |  | inherited |
| TX1:088 | crates/aspis-r1-cost-probe/src/candidate.rs::query_loop | CLOSED | (ae) | NFS |
| TX1:089 | crates/aspis-r1-cost-probe/src/candidate.rs::query_values | CLOSED | (ae) | NFS |
| TX1:090 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index | OPEN |  | inherited |
| TX1:091 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf | OPEN |  | inherited |
| TX1:092 | crates/aspis-r1-cost-probe/src/candidate.rs::slot | OPEN |  | inherited |
| TX1:093 | crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys | OPEN |  | inherited |
| TX1:094 | crates/aspis-r1-cost-probe/src/candidate.rs::tx1 | OPEN |  | inherited |
| TX1:095 | crates/aspis-r1-cost-probe/src/candidate.rs::wide_view | CLOSED | (y)/(ai) | NHF |
| TX1:096 | crates/aspis-r1-cost-probe/src/compact.rs::check_values | CLOSED | (y) | NFU |
| TX1:097 | crates/aspis-r1-cost-probe/src/compact.rs::compact_row | CLOSED | (y) plain | NFQ |
| TX1:098 | crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic | CLOSED | (y) | NGV |
| TX1:099 | crates/aspis-r1-cost-probe/src/compact.rs::expand_values | CLOSED | (y) | NFU |
| TX1:100 | crates/aspis-r1-cost-probe/src/compact.rs::slot_offset | CLOSED | (y) | NGD |
| TX1:101 | crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point | CLOSED | (y) plain | Q |
| TX1:102 | crates/aspis-r1-cost-probe/src/fast_domain.rs::line_node | CLOSED | (y) plain | Q |
| TX1:103 | crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value | CLOSED | (y) plain | Q |
| TX1:104 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots | CLOSED | (ad) | NFM |
| TX1:105 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one | CLOSED | (ad) | NFM |
| TX1:106 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish | CLOSED | (y) plain | Q |
| TX1:107 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new | CLOSED | (y) plain | Q |
| TX1:108 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push | CLOSED | (y) plain | NFG |
| TX1:109 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::finish | CLOSED | (y) plain | Q |
| TX1:110 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new | CLOSED | (y) plain | Q |
| TX1:111 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push | CLOSED | (y) plain | NFG |
| TX1:112 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_limbs | CLOSED | (y) plain | Q |
| TX1:113 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_wide | CLOSED | (y) plain | Q |
| TX1:114 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::limbs | CLOSED | (y) plain | Q |
| TX1:115 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::reduce | CLOSED | (y) plain | Q |
| TX1:116 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::checked_q | CLOSED | (y) plain | Q |
| TX1:117 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::limbs_of | CLOSED | (y) plain | Q |
| TX1:118 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits | OPEN |  | inherited |
| TX1:119 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels | OPEN |  | inherited |
| TX1:120 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width | OPEN |  | inherited |
| TX1:121 | crates/aspis-r1-cost-probe/src/multiproof.rs::index_at | OPEN |  | inherited |
| TX1:122 | crates/aspis-r1-cost-probe/src/multiproof.rs::node_count | OPEN |  | inherited |
| TX1:123 | crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent | OPEN |  | inherited |
| TX1:124 | crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches | OPEN |  | inherited |
| TX1:125 | crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent | OPEN |  | inherited |
| TX1:126 | crates/aspis-r1-cost-probe/src/multiproof.rs::value_at | OPEN |  | inherited |
| TX1:127 | crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place | OPEN |  | inherited |
| TX1:128 | crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed | OPEN |  | inherited |
| TX1:129 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::claims | OPEN |  | inherited |
| TX1:130 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::mark | OPEN |  | inherited |
| TX1:131 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::public_transcript | OPEN |  | inherited |
| TX1:132 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_boundary | OPEN |  | inherited |
| TX1:133 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_round | OPEN |  | inherited |
| TX1:134 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_rounds | OPEN |  | inherited |
| TX1:135 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::semantic_value | OPEN |  | inherited |
| TX1:136 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_finish | OPEN |  | inherited |
| TX1:137 | crates/aspis-r1-cost-probe/src/r1_semantic.rs::verify_observed | OPEN |  | inherited |
| TX1:138 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::parse | CLOSED | (y) | NGX |
| TX1:139 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::payload | CLOSED | (y) | NGX |
| TX1:140 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::record | CLOSED | (y) | NFU |
| TX1:141 | crates/aspis-r1-cost-probe/src/r1_wire.rs::Prefix<'a>::validated_record | CLOSED | (y) | NFU |
| TX1:142 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::circle_validated | OPEN |  | inherited |
| TX1:143 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::new | CLOSED | (y) | NGX |
| TX1:144 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::sample_block_validated | CLOSED | (y) | NGX |
| TX1:145 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::semantic_validated | CLOSED | (y) | NGX |
| TX1:146 | crates/aspis-r1-cost-probe/src/r1_wire.rs::SemanticTranscript<H>::state | CLOSED | (y) | NGX |
| TX1:147 | crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k | CLOSED | (y) | NGO |
| TX1:148 | crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::framed | CLOSED | (y) | NFU |
| TX1:149 | crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::row | CLOSED | (y) | NFU |
| TX1:150 | crates/aspis-r1-cost-probe/src/r1_wire.rs::begin | OPEN |  | inherited |
| TX1:151 | crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record | CLOSED | (y) | NGV |
| TX1:152 | crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record_at | CLOSED | (y) | NGV |
| TX1:153 | crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape | CLOSED | (y) plain | NFQ |
| TX1:154 | crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields | CLOSED | (y) | NFU |
| TX1:155 | crates/aspis-r1-cost-probe/src/sampler.rs::add_small_base_p | OPEN |  | inherited |
| TX1:156 | crates/aspis-r1-cost-probe/src/sampler.rs::circle_sample | OPEN |  | inherited |
| TX1:157 | crates/aspis-r1-cost-probe/src/sampler.rs::decode8 | OPEN |  | inherited |
| TX1:158 | crates/aspis-r1-cost-probe/src/sampler.rs::gamma_sample | OPEN |  | inherited |
| TX1:159 | crates/aspis-r1-cost-probe/src/sampler.rs::low_base_p_digits | OPEN |  | inherited |
| TX1:160 | crates/aspis-r1-cost-probe/src/sampler.rs::ordinary_sample | OPEN |  | inherited |
| TX1:161 | crates/aspis-r1-cost-probe/src/sampler.rs::qm31_digits | CLOSED | (y) | NGX |
| TX1:162 | crates/aspis-r1-cost-probe/src/sampler.rs::qm31_div_pass | CLOSED | (y) | NGX |
| TX1:163 | crates/aspis-r1-cost-probe/src/sampler.rs::qm31_sample | CLOSED | (y) | NGX |
| TX1:164 | crates/aspis-r1-cost-probe/src/trace.rs::value | CLOSED | (y) plain | Q |
| TX1:165 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::absorb | OPEN |  | inherited |
| TX1:166 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::block | OPEN |  | inherited |
| TX1:167 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::new | OPEN |  | inherited |
| TX1:168 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::queries | OPEN |  | inherited |
| TX1:169 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar | CLOSED | (y)/(ai) | NGT |
| TX1:170 | crates/aspis-r1-cost-probe/src/transcript.rs::Transcript<H>::scalar_k | CLOSED | (y)/(ai) | NGT |
| TX1:171 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len | CLOSED | (y) plain | NFQ |
| TX1:172 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::folds | CLOSED | (y) plain | NFQ |
| TX1:173 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag | CLOSED | (y) plain | NFY |
| TX1:174 | crates/aspis-r1-cost-probe/src/verifier.rs::Accumulator::new | CLOSED | (y) | NGC |
| TX1:175 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish | CLOSED | (y) | NGC |
| TX1:176 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new | OPEN |  | inherited |
| TX1:177 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::push | CLOSED | (y) plain | Q |
| TX1:178 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value | CLOSED | (y) | NGC |
| TX1:179 | crates/aspis-r1-cost-probe/src/verifier.rs::Prepared::new | OPEN |  | inherited |
| TX1:180 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query | CLOSED | (y) plain | Q |
| TX1:181 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range | CLOSED | (y) plain | NFN |
| TX1:182 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node | CLOSED | (y) plain | NFC |
| TX1:183 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulated_weight_at | CLOSED | (y) plain | Q |
| TX1:184 | crates/aspis-r1-cost-probe/src/verifier.rs::basis_at | CLOSED | (y) plain | Q |
| TX1:185 | crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products | CLOSED | (y) plain | NFC |
| TX1:186 | crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint | OPEN |  | inherited |
| TX1:187 | crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size | CLOSED | (y) plain | NFQ |
| TX1:188 | crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses | CLOSED | reclassification | Q |
| TX1:189 | crates/aspis-r1-cost-probe/src/verifier.rs::echeck | OPEN |  | inherited |
| TX1:190 | crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses | CLOSED | reclassification | Q |
| TX1:191 | crates/aspis-r1-cost-probe/src/verifier.rs::mark | CLOSED | reclassification | Q |
| TX1:192 | crates/aspis-r1-cost-probe/src/verifier.rs::power_limb_at | CLOSED | (y) plain | Q |
| TX1:193 | crates/aspis-r1-cost-probe/src/verifier.rs::prepared_claim | CLOSED | (ah) | NGY |
| TX1:194 | crates/aspis-r1-cost-probe/src/verifier.rs::residue_limb_at | CLOSED | (y) plain | Q |
| TX1:195 | crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row | CLOSED | (y) plain | Q |
| TX1:196 | crates/aspis-r1-cost-probe/src/weights.rs::field | CLOSED | (y) plain | Q |
| TX1:197 | crates/aspis-r1-cost-probe/src/weights.rs::powers | CLOSED | (y) | NFW |
| TX1:198 | crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical | CLOSED | (y) plain | NGE |
| TX1:199 | crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical | CLOSED | (y) plain | NGE |
| TX1:200 | crates/aspis-statement/src/atomic_statement.rs::unwrap_fixed_slice | CLOSED | (y) plain | S |
| TX1:201 | crates/aspis-statement/src/pool_v1/format.rs::pool_v1_tree_parent | OPEN |  | inherited |
| TX1:202 | crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::default | OPEN |  | inherited |
| TX1:203 | crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::empty | OPEN |  | inherited |
| TX1:204 | crates/aspis-statement/src/pool_v1/incremental_merkle.rs::pool_v1_empty_roots | OPEN |  | inherited |
| TX1:205 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical | CLOSED | (y) plain | NGE |
| TX1:206 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte | CLOSED | (y) plain | NGE |
| TX1:207 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 | CLOSED | (y) plain | NGE |
| TX1:208 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active | OPEN |  | inherited |
| TX1:209 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::active_mask_basis | OPEN |  | inherited |
| TX1:210 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::at_point | OPEN |  | inherited |
| TX1:211 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::boxed_at_point | OPEN |  | inherited |
| TX1:212 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::expand | OPEN |  | inherited |
| TX1:213 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::Selectors::row | OPEN |  | inherited |
| TX1:214 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::accumulate_endpoint_selector_tensor_basis | OPEN |  | inherited |
| TX1:215 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_residual | OPEN |  | inherited |
| TX1:216 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_dot | OPEN |  | inherited |
| TX1:217 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::copy_tag_coordinate_value | OPEN |  | inherited |
| TX1:218 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::evaluate_with_selectors | OPEN |  | inherited |
| TX1:219 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_pattern_basis_values | OPEN |  | inherited |
| TX1:220 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::finish_selector_tensor_basis | OPEN |  | inherited |
| TX1:221 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::lift_m31 | OPEN |  | inherited |
| TX1:222 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::link_weight | OPEN |  | inherited |
| TX1:223 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values | OPEN |  | inherited |
| TX1:224 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::pattern_values_windowed | OPEN |  | inherited |
| TX1:225 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::qm31_sum_products_up_to4 | OPEN |  | inherited |
| TX1:226 | crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs::selected_binary_weight | OPEN |  | inherited |
| TX1:227 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::absorption_lanes_factored | OPEN |  | inherited |
| TX1:228 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_occupancy_lanes | OPEN |  | inherited |
| TX1:229 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_path_lanes | OPEN |  | inherited |
| TX1:230 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted | OPEN |  | inherited |
| TX1:231 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_preweighted_shared_selector | OPEN |  | inherited |
| TX1:232 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_schedule_lanes | OPEN |  | inherited |
| TX1:233 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::add_value_lanes | OPEN |  | inherited |
| TX1:234 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_level_packed_selector_tensor | OPEN |  | inherited |
| TX1:235 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::append_levels_packed_selector_tensor | OPEN |  | inherited |
| TX1:236 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::bounded_append_carry | OPEN |  | inherited |
| TX1:237 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::composition_parts | OPEN |  | inherited |
| TX1:238 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::copy_variant | CLOSED | (y) plain | NFQ |
| TX1:239 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::empty_root | OPEN |  | inherited |
| TX1:240 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::equality_value | OPEN |  | inherited |
| TX1:241 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::initial_variant_selectors | OPEN |  | inherited |
| TX1:242 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::left_digest_packed_selector_tensor | OPEN |  | inherited |
| TX1:243 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::lift_m31 | OPEN |  | inherited |
| TX1:244 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::occupancy_lanes_factored | OPEN |  | inherited |
| TX1:245 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_carry_packed_selector_tensor | OPEN |  | inherited |
| TX1:246 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::optional_recipient_packed_selector_tensor | OPEN |  | inherited |
| TX1:247 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::path_lanes_factored | OPEN |  | inherited |
| TX1:248 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::poseidon_selectors | OPEN |  | inherited |
| TX1:249 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::private_public | OPEN |  | inherited |
| TX1:250 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed | OPEN |  | inherited |
| TX1:251 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::public_digest_packed_selector_tensor | OPEN |  | inherited |
| TX1:252 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::fields | OPEN |  | inherited |
| TX1:253 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes::frontier | OPEN |  | inherited |
| TX1:254 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::public_bytes | OPEN |  | inherited |
| TX1:255 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::semantic | OPEN |  | inherited |
| TX1:256 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::r0::Public<'a>::terminal_qm31 | OPEN |  | inherited |
| TX1:257 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::reconstruct_10 | OPEN |  | inherited |
| TX1:258 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::scalar_lanes | OPEN |  | inherited |
| TX1:259 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::selected_claim | OPEN |  | inherited |
| TX1:260 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_initial_and_absorption | OPEN |  | inherited |
| TX1:261 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::semantic_packed | OPEN |  | inherited |
| TX1:262 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::sum_high | OPEN |  | inherited |
| TX1:263 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::terminal_parts | OPEN |  | inherited |
| TX1:264 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::validate_transition | OPEN |  | inherited |
| TX1:265 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::variant_expected_output | CLOSED | (y) plain | NFQ |
| TX1:266 | crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::withdrawal_public | OPEN |  | inherited |
| TX1:267 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common | CLOSED | (y) plain | NFY |
| TX1:268 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public | OPEN |  | inherited |
| TX1:269 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_lane_transition_boxed_v1 | CLOSED | (y) plain | NGI |
| TX1:270 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_statement_v1 | CLOSED | (y) plain | NGI |
| TX1:271 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_terminal_common_boxed_v1 | CLOSED | (y) plain | NGI |
| TX1:272 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_transfer_statement_boxed_v1 | CLOSED | (y) plain | NGE |
| TX1:273 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_withdrawal_statement_boxed_v1 | CLOSED | (y) plain | NGE |
| TX1:274 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::statement_public_common | CLOSED | (y) plain | NFY |
| TX1:275 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind | CLOSED | (y) plain | NGE |
| TX1:276 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 | CLOSED | (y) plain | NGE |
| TX1:277 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1 | CLOSED | (y) plain | NGI |
| TX1:278 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 | CLOSED | (y) plain | NGE |
| TX1:279 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact | CLOSED | (y) plain | S |
| TX1:280 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate | CLOSED | (y) plain | NGE |
| TX1:281 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_afterstate_boxed_v1 | CLOSED | (y) plain | NGI |
| TX1:282 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_live_snapshot_boxed_v1 | CLOSED | (y) plain | NGI |
| TX1:283 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_late_public_statement_boxed_v1 | CLOSED | (y) plain | NGI |
| TX1:284 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_live_snapshot_v1 | CLOSED | (y) plain | NGI |
| TX1:285 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical | CLOSED | (y) plain | NGE |
| TX1:286 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1 | CLOSED | (y) plain | NGE |
| TX1:287 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1 | CLOSED | (y) plain | NGE |
| TX1:288 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1 | CLOSED | (y) plain | NGE |
| TX1:289 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common | CLOSED | (y) plain | NGE |
| TX1:290 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1 | CLOSED | (y) plain | NGE |
| TX1:291 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1 | CLOSED | (y) plain | NGE |
| TX1:292 | crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical | CLOSED | (y) plain | NFY |
| TX1:293 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common | CLOSED | (y) plain | NGE |
| TX1:294 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1 | CLOSED | (y) plain | NGE |
| TX1:295 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1 | CLOSED | (y) plain | NGE |
| TX1:296 | crates/aspis-statement/src/pool_v1/payment_relation.rs::require_header | CLOSED | (y) plain | NFY |
| TX1:297 | crates/aspis-statement/src/pool_v1/payment_relation.rs::transfer_common | CLOSED | (y) plain | NFY |
| TX1:298 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common | CLOSED | (y) plain | NGE |
| TX1:299 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1 | CLOSED | (y) plain | NGE |
| TX1:300 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1 | CLOSED | (y) plain | NGE |
| TX1:301 | crates/aspis-statement/src/pool_v1/payment_relation.rs::withdrawal_common | CLOSED | (y) plain | NFY |
| TX1:302 | crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy | OPEN |  | inherited |
| TX1:303 | crates/aspis-statement/src/poseidon2.rs::external_linear_lazy | OPEN |  | inherited |
| TX1:304 | crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy | OPEN |  | inherited |
| TX1:305 | crates/aspis-statement/src/poseidon2.rs::merkle_node_compress_v3 | OPEN |  | inherited |
| TX1:306 | crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace | OPEN |  | inherited |
| TX1:307 | crates/aspis-statement/src/poseidon2.rs::pow5 | OPEN |  | inherited |
| TX1:308 | crates/aspis-statement/src/state_only_poseidon.rs::evaluate_state_only_poseidon_oracle_projected | OPEN |  | inherited |
| TX1:309 | crates/aspis-statement/src/state_only_poseidon.rs::extension_from_raw_limbs | OPEN |  | inherited |
| TX1:310 | crates/aspis-statement/src/state_only_poseidon.rs::extension_limbs | CLOSED | (y) plain | NFQ |
| TX1:311 | crates/aspis-statement/src/state_only_poseidon.rs::external_linear_lazy | OPEN |  | inherited |
| TX1:312 | crates/aspis-statement/src/state_only_poseidon.rs::external_linear_packed | OPEN |  | inherited |
| TX1:313 | crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed | OPEN |  | inherited |
| TX1:314 | crates/aspis-statement/src/state_only_poseidon.rs::external_local_packed_raw | OPEN |  | inherited |
| TX1:315 | crates/aspis-statement/src/state_only_poseidon.rs::full_round | OPEN |  | inherited |
| TX1:316 | crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants | OPEN |  | inherited |
| TX1:317 | crates/aspis-statement/src/state_only_poseidon.rs::full_round_m31_constants_packed | OPEN |  | inherited |
| TX1:318 | crates/aspis-statement/src/state_only_poseidon.rs::full_round_packed | OPEN |  | inherited |
| TX1:319 | crates/aspis-statement/src/state_only_poseidon.rs::internal_linear_lazy | OPEN |  | inherited |
| TX1:320 | crates/aspis-statement/src/state_only_poseidon.rs::internal_round | OPEN |  | inherited |
| TX1:321 | crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_columns | OPEN |  | inherited |
| TX1:322 | crates/aspis-statement/src/state_only_poseidon.rs::interpolate_three_constant_limb | OPEN |  | inherited |
| TX1:323 | crates/aspis-statement/src/state_only_poseidon.rs::interpolated_full_pair_packed | OPEN |  | inherited |
| TX1:324 | crates/aspis-statement/src/state_only_poseidon.rs::interpolated_internal_pair | OPEN |  | inherited |
| TX1:325 | crates/aspis-statement/src/state_only_poseidon.rs::leading_pair_packed | OPEN |  | inherited |
| TX1:326 | crates/aspis-statement/src/state_only_poseidon.rs::pow5 | OPEN |  | inherited |
| TX1:327 | programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest | CLOSED | (y) | NGC |
| TX1:328 | programs/r1-cost-probe/src/lib.rs::first_decoded | OPEN |  | inherited |
| TX1:329 | programs/r1-cost-probe/src/lib.rs::observer | OPEN |  | inherited |
| TX1:330 | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction | OPEN |  | inherited |
| TX1:331 | programs/r1-cost-probe/src/pool_route.rs::admitted | OPEN |  | inherited |
| TX1:332 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box | CLOSED | (y) plain | NGI |
| TX1:333 | programs/r1-cost-probe/src/r1_pool_adapter.rs::process | OPEN |  | inherited |
| TX1:334 | programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok | CLOSED | (y) plain | NFQ |
| TX1:335 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data | OPEN |  | inherited |
| TX1:336 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len | OPEN |  | inherited |
| TX1:337 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key | CLOSED | (y) | NFU |
| TX1:338 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner | CLOSED | (y) | NFU |
| TX1:339 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts | OPEN |  | inherited |
| TX1:340 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer | CLOSED | (y) | NFU |
| TX1:341 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint | OPEN |  | inherited |
| TX1:342 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero | CLOSED | (y) | NFU |
| TX1:343 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot | OPEN |  | inherited |
| TX1:344 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1 | OPEN |  | inherited |
| TX1:345 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned | OPEN |  | inherited |
| TX2:001 | crates/aspis-core/src/field.rs::CM31::add | CLOSED | (y) plain | Q |
| TX2:002 | crates/aspis-core/src/field.rs::CM31::double | CLOSED | (y) plain | Q |
| TX2:003 | crates/aspis-core/src/field.rs::CM31::from_le_bytes | CLOSED | (y) plain | Q |
| TX2:004 | crates/aspis-core/src/field.rs::CM31::mul | CLOSED | (y) plain | Q |
| TX2:005 | crates/aspis-core/src/field.rs::CM31::mul_m31 | CLOSED | (y) plain | Q |
| TX2:006 | crates/aspis-core/src/field.rs::CM31::new | CLOSED | (y) plain | Q |
| TX2:007 | crates/aspis-core/src/field.rs::CM31::sub | CLOSED | (y) plain | Q |
| TX2:008 | crates/aspis-core/src/field.rs::CM31::write_le_bytes | CLOSED | (y) | NFT |
| TX2:009 | crates/aspis-core/src/field.rs::M31::add | CLOSED | (y) plain | Q |
| TX2:010 | crates/aspis-core/src/field.rs::M31::double | CLOSED | (y) plain | Q |
| TX2:011 | crates/aspis-core/src/field.rs::M31::from_le_bytes | CLOSED | (y) plain | S |
| TX2:012 | crates/aspis-core/src/field.rs::M31::inv | CLOSED | (y) plain | NEW |
| TX2:013 | crates/aspis-core/src/field.rs::M31::mul | CLOSED | (y) plain | Q |
| TX2:014 | crates/aspis-core/src/field.rs::M31::reduce_u64 | CLOSED | (y) plain | Q |
| TX2:015 | crates/aspis-core/src/field.rs::M31::sub | CLOSED | (y) plain | Q |
| TX2:016 | crates/aspis-core/src/field.rs::M31::to_le_bytes | CLOSED | (y) plain | NFY |
| TX2:017 | crates/aspis-core/src/field.rs::QM31::add | CLOSED | (y) plain | Q |
| TX2:018 | crates/aspis-core/src/field.rs::QM31::from_cm31 | CLOSED | (y) plain | NFQ |
| TX2:019 | crates/aspis-core/src/field.rs::QM31::from_le_bytes | CLOSED | (y) plain | Q |
| TX2:020 | crates/aspis-core/src/field.rs::QM31::mul | CLOSED | (y) plain | Q |
| TX2:021 | crates/aspis-core/src/field.rs::QM31::mul_m31 | CLOSED | (y) plain | Q |
| TX2:022 | crates/aspis-core/src/field.rs::QM31::square | CLOSED | (y) | NGH |
| TX2:023 | crates/aspis-core/src/field.rs::QM31::sub | CLOSED | (y) plain | Q |
| TX2:024 | crates/aspis-core/src/field.rs::QM31::write_le_bytes | CLOSED | (y) | NFT |
| TX2:025 | crates/aspis-core/src/field.rs::mul_by_r | CLOSED | (y) plain | Q |
| TX2:026 | crates/aspis-core/src/field.rs::reduce_u64 | CLOSED | (y) plain | Q |
| TX2:027 | crates/aspis-core/src/field.rs::square_n | CLOSED | (y) plain | Q |
| TX2:028 | crates/aspis-core/src/field/wide_exact.rs::WideExact::add | CLOSED | (y) plain | Q |
| TX2:029 | crates/aspis-core/src/field/wide_exact.rs::WideExact::c0 | CLOSED | (y) plain | NFQ |
| TX2:030 | crates/aspis-core/src/field/wide_exact.rs::WideExact::c1 | CLOSED | (y) plain | NFQ |
| TX2:031 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_le_bytes | CLOSED | (y) plain | Q |
| TX2:032 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs | CLOSED | (y) plain | Q |
| TX2:033 | crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31 | CLOSED | (y) plain | Q |
| TX2:034 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul | CLOSED | (y) plain | Q |
| TX2:035 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_m31 | CLOSED | (y) plain | Q |
| TX2:036 | crates/aspis-core/src/field/wide_exact.rs::WideExact::mul_qm31 | CLOSED | (y) plain | Q |
| TX2:037 | crates/aspis-core/src/field/wide_exact.rs::WideExact::new | CLOSED | (y) | NFT |
| TX2:038 | crates/aspis-core/src/field/wide_exact.rs::WideExact::sub | CLOSED | (y) plain | Q |
| TX2:039 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes | CLOSED | (y) plain | NFY |
| TX2:040 | crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs | CLOSED | (y) plain | Q |
| TX2:041 | crates/aspis-core/src/field/wide_exact.rs::canonical_qm31 | CLOSED | (y) plain | Q |
| TX2:042 | crates/aspis-core/src/field/wide_exact.rs::mul_u | CLOSED | (y) plain | Q |
| TX2:043 | crates/aspis-core/src/r0/domain.rs::FibreIndex::get | CLOSED | (y) plain | Q |
| TX2:044 | crates/aspis-core/src/r0/domain.rs::FibreIndex::new | CLOSED | (y) plain | Q |
| TX2:045 | crates/aspis-core/src/r0/heap.rs::filled | CLOSED | (y) | NGC |
| TX2:046 | crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31 | CLOSED | (y) | NHH |
| TX2:047 | crates/aspis-core/src/state_only_prefix.rs::r0::statement_points | CLOSED | (y) | NGW |
| TX2:048 | crates/aspis-core/src/state_only_prefix.rs::state_only_statement_points | CLOSED | (y) | NGW |
| TX2:049 | crates/aspis-core/src/state_only_private_merkle.rs::private_leaf_hash_with_digest | OPEN |  | inherited |
| TX2:050 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_key_at | OPEN |  | inherited |
| TX2:051 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_keys | OPEN |  | inherited |
| TX2:052 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_leaf | OPEN |  | inherited |
| TX2:053 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle | OPEN |  | inherited |
| TX2:054 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_merkle_values | OPEN |  | inherited |
| TX2:055 | crates/aspis-r1-cost-probe/src/candidate.rs::batch_tree | OPEN |  | inherited |
| TX2:056 | crates/aspis-r1-cost-probe/src/candidate.rs::opening | CLOSED | (y) plain | Q |
| TX2:057 | crates/aspis-r1-cost-probe/src/candidate.rs::parse_shape | OPEN |  | inherited |
| TX2:058 | crates/aspis-r1-cost-probe/src/candidate.rs::query_loop | CLOSED | (ae) | NFS |
| TX2:059 | crates/aspis-r1-cost-probe/src/candidate.rs::query_values | CLOSED | (ae) | NFS |
| TX2:060 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_index | OPEN |  | inherited |
| TX2:061 | crates/aspis-r1-cost-probe/src/candidate.rs::same_batch_leaf | OPEN |  | inherited |
| TX2:062 | crates/aspis-r1-cost-probe/src/candidate.rs::slot | OPEN |  | inherited |
| TX2:063 | crates/aspis-r1-cost-probe/src/candidate.rs::sort_batch_keys | OPEN |  | inherited |
| TX2:064 | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated | OPEN |  | inherited |
| TX2:065 | crates/aspis-r1-cost-probe/src/candidate.rs::tx2_common | OPEN |  | inherited |
| TX2:066 | crates/aspis-r1-cost-probe/src/compact.rs::slot_offset | CLOSED | (y) | NGD |
| TX2:067 | crates/aspis-r1-cost-probe/src/fast_domain.rs::fibre_point | CLOSED | (y) plain | Q |
| TX2:068 | crates/aspis-r1-cost-probe/src/fast_domain.rs::line_node | CLOSED | (y) plain | Q |
| TX2:069 | crates/aspis-r1-cost-probe/src/fast_domain.rs::table_value | CLOSED | (y) plain | Q |
| TX2:070 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots | CLOSED | (ad) | NFM |
| TX2:071 | crates/aspis-r1-cost-probe/src/fast_dots.rs::four_dots_one | CLOSED | (ad) | NFM |
| TX2:072 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish | CLOSED | (y) plain | Q |
| TX2:073 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new | CLOSED | (y) plain | Q |
| TX2:074 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push | CLOSED | (y) plain | NFG |
| TX2:075 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::finish | CLOSED | (y) plain | Q |
| TX2:076 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::new | CLOSED | (y) plain | Q |
| TX2:077 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Dot::push | CLOSED | (y) plain | NFG |
| TX2:078 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_limbs | CLOSED | (y) plain | Q |
| TX2:079 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::from_wide | CLOSED | (y) plain | Q |
| TX2:080 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::Q::limbs | CLOSED | (y) plain | Q |
| TX2:081 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::canonical::reduce | CLOSED | (y) plain | Q |
| TX2:082 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::checked_q | CLOSED | (y) plain | Q |
| TX2:083 | crates/aspis-r1-cost-probe/src/fast_pairing.rs::limbs_of | CLOSED | (y) plain | Q |
| TX2:084 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::bits | OPEN |  | inherited |
| TX2:085 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::levels | OPEN |  | inherited |
| TX2:086 | crates/aspis-r1-cost-probe/src/multiproof.rs::Arity::width | OPEN |  | inherited |
| TX2:087 | crates/aspis-r1-cost-probe/src/multiproof.rs::index_at | OPEN |  | inherited |
| TX2:088 | crates/aspis-r1-cost-probe/src/multiproof.rs::node_count | OPEN |  | inherited |
| TX2:089 | crates/aspis-r1-cost-probe/src/multiproof.rs::occupied_binary_parent | OPEN |  | inherited |
| TX2:090 | crates/aspis-r1-cost-probe/src/multiproof.rs::root_matches | OPEN |  | inherited |
| TX2:091 | crates/aspis-r1-cost-probe/src/multiproof.rs::sibling_binary_parent | OPEN |  | inherited |
| TX2:092 | crates/aspis-r1-cost-probe/src/multiproof.rs::value_at | OPEN |  | inherited |
| TX2:093 | crates/aspis-r1-cost-probe/src/multiproof.rs::verify_in_place | OPEN |  | inherited |
| TX2:094 | crates/aspis-r1-cost-probe/src/multiproof.rs::well_formed | OPEN |  | inherited |
| TX2:095 | crates/aspis-r1-cost-probe/src/trace.rs::value | CLOSED | (y) plain | Q |
| TX2:096 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len | CLOSED | (y) plain | NFQ |
| TX2:097 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::folds | CLOSED | (y) plain | NFQ |
| TX2:098 | crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag | CLOSED | (y) plain | NFY |
| TX2:099 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::finish | OPEN |  | inherited |
| TX2:100 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::new | OPEN |  | inherited |
| TX2:101 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::push | CLOSED | (y) plain | Q |
| TX2:102 | crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value | OPEN |  | inherited |
| TX2:103 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_query | CLOSED | (y) plain | Q |
| TX2:104 | crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range | CLOSED | (y) plain | NFN |
| TX2:105 | crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::e | OPEN |  | inherited |
| TX2:106 | crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::k | OPEN |  | inherited |
| TX2:107 | crates/aspis-r1-cost-probe/src/verifier.rs::Reader<'a>::raw | OPEN |  | inherited |
| TX2:108 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulate_batched_with_node | CLOSED | (y) plain | NFC |
| TX2:109 | crates/aspis-r1-cost-probe/src/verifier.rs::accumulated_weight_at | CLOSED | (y) plain | Q |
| TX2:110 | crates/aspis-r1-cost-probe/src/verifier.rs::basis_at | CLOSED | (y) plain | Q |
| TX2:111 | crates/aspis-r1-cost-probe/src/verifier.rs::batch_prefix_products | CLOSED | (y) plain | NFC |
| TX2:112 | crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size | CLOSED | (y) plain | NFQ |
| TX2:113 | crates/aspis-r1-cost-probe/src/verifier.rs::circle_fold_with_inverses | CLOSED | reclassification | Q |
| TX2:114 | crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot | CLOSED | (y) | NHE |
| TX2:115 | crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation | OPEN |  | inherited |
| TX2:116 | crates/aspis-r1-cost-probe/src/verifier.rs::finish_relation_round | CLOSED | (y) | NHE |
| TX2:117 | crates/aspis-r1-cost-probe/src/verifier.rs::line_fold_with_inverses | CLOSED | reclassification | Q |
| TX2:118 | crates/aspis-r1-cost-probe/src/verifier.rs::mark | CLOSED | reclassification | Q |
| TX2:119 | crates/aspis-r1-cost-probe/src/verifier.rs::polynomial | CLOSED | (ah) | NHE |
| TX2:120 | crates/aspis-r1-cost-probe/src/verifier.rs::power_limb_at | CLOSED | (y) plain | Q |
| TX2:121 | crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_semantic_alpha | OPEN |  | inherited |
| TX2:122 | crates/aspis-r1-cost-probe/src/verifier.rs::read_checkpoint_weights | OPEN |  | inherited |
| TX2:123 | crates/aspis-r1-cost-probe/src/verifier.rs::residue_limb_at | CLOSED | (y) plain | Q |
| TX2:124 | crates/aspis-r1-cost-probe/src/verifier.rs::resume | OPEN |  | inherited |
| TX2:125 | crates/aspis-r1-cost-probe/src/verifier.rs::update_residue_row | CLOSED | (y) plain | Q |
| TX2:126 | crates/aspis-r1-cost-probe/src/verifier.rs::validate_checkpoint_queries | OPEN |  | inherited |
| TX2:127 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::box_from_parts | CLOSED | (y) | NGW |
| TX2:128 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::new | CLOSED | (y) | NGW |
| TX2:129 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::pair | OPEN |  | inherited |
| TX2:130 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::scalar_factor | CLOSED | (y) | NHI |
| TX2:131 | crates/aspis-r1-cost-probe/src/weights.rs::Weights::tensor | CLOSED | (y) | NHI |
| TX2:132 | crates/aspis-r1-cost-probe/src/weights.rs::double | CLOSED | (y) | NGM |
| TX2:133 | crates/aspis-r1-cost-probe/src/weights.rs::factored_s2_libra_weights | OPEN |  | inherited |
| TX2:134 | crates/aspis-r1-cost-probe/src/weights.rs::field | CLOSED | (y) plain | Q |
| TX2:135 | crates/aspis-r1-cost-probe/src/weights.rs::grouped_inactive_pair | OPEN |  | inherited |
| TX2:136 | crates/aspis-r1-cost-probe/src/weights.rs::high_dot | OPEN |  | inherited |
| TX2:137 | crates/aspis-r1-cost-probe/src/weights.rs::partial_dot | OPEN |  | inherited |
| TX2:138 | crates/aspis-r1-cost-probe/src/weights.rs::powers | CLOSED | (y) | NFW |
| TX2:139 | crates/aspis-r1-cost-probe/src/weights.rs::process_kind | OPEN |  | inherited |
| TX2:140 | crates/aspis-r1-cost-probe/src/weights.rs::process_regular_kinds | OPEN |  | inherited |
| TX2:141 | crates/aspis-r1-cost-probe/src/weights.rs::push_byte_products | OPEN |  | inherited |
| TX2:142 | crates/aspis-r1-cost-probe/src/weights.rs::s2_grouped_inactive_pair | OPEN |  | inherited |
| TX2:143 | crates/aspis-r1-cost-probe/src/weights.rs::shared_high | OPEN |  | inherited |
| TX2:144 | crates/aspis-r1-cost-probe/src/weights.rs::shared_partials | OPEN |  | inherited |
| TX2:145 | crates/aspis-r1-cost-probe/src/weights.rs::shared_two_point_guard | CLOSED | (y) | NGM |
| TX2:146 | crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical | CLOSED | (y) plain | NGE |
| TX2:147 | crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical | CLOSED | (y) plain | NGE |
| TX2:148 | crates/aspis-statement/src/atomic_statement.rs::unwrap_fixed_slice | CLOSED | (y) plain | S |
| TX2:149 | crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1 | OPEN |  | inherited |
| TX2:150 | crates/aspis-statement/src/pool_v1/format.rs::decode_verifier_policy_v1 | OPEN |  | inherited |
| TX2:151 | crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1 | OPEN |  | inherited |
| TX2:152 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1 | OPEN |  | inherited |
| TX2:153 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1 | OPEN |  | inherited |
| TX2:154 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical | CLOSED | (y) plain | NGE |
| TX2:155 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte | CLOSED | (y) plain | NGE |
| TX2:156 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 | CLOSED | (y) plain | NGE |
| TX2:157 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::validate_master | OPEN |  | inherited |
| TX2:158 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier | CLOSED | (y) plain | NGE |
| TX2:159 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind | CLOSED | (y) plain | NGE |
| TX2:160 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common | CLOSED | (y) plain | NFY |
| TX2:161 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier | CLOSED | (y) plain | NGE |
| TX2:162 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::transition_kind | CLOSED | (y) plain | NGE |
| TX2:163 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1 | CLOSED | (y) plain | NGE |
| TX2:164 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1 | CLOSED | (y) plain | NGI |
| TX2:165 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1 | CLOSED | (y) plain | NGE |
| TX2:166 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::statement_public_common | CLOSED | (y) plain | NFY |
| TX2:167 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind | CLOSED | (y) plain | NGE |
| TX2:168 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1 | CLOSED | (y) plain | NGI |
| TX2:169 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 | CLOSED | (y) plain | NGE |
| TX2:170 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_result | CLOSED | (y) plain | NGE |
| TX2:171 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1 | CLOSED | (y) plain | NGI |
| TX2:172 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 | CLOSED | (y) plain | NGE |
| TX2:173 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact | CLOSED | (y) plain | S |
| TX2:174 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate | CLOSED | (y) plain | NGE |
| TX2:175 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical | CLOSED | (y) plain | NGE |
| TX2:176 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1 | CLOSED | (y) plain | NGE |
| TX2:177 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1 | CLOSED | (y) plain | NGE |
| TX2:178 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1 | CLOSED | (y) plain | NGE |
| TX2:179 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common | CLOSED | (y) plain | NGE |
| TX2:180 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1 | CLOSED | (y) plain | NGE |
| TX2:181 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1 | CLOSED | (y) plain | NGE |
| TX2:182 | crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical | CLOSED | (y) plain | NFY |
| TX2:183 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common | CLOSED | (y) plain | NGE |
| TX2:184 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1 | CLOSED | (y) plain | NGE |
| TX2:185 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1 | CLOSED | (y) plain | NGE |
| TX2:186 | crates/aspis-statement/src/pool_v1/payment_relation.rs::require_header | CLOSED | (y) plain | NFY |
| TX2:187 | crates/aspis-statement/src/pool_v1/payment_relation.rs::transfer_common | CLOSED | (y) plain | NFY |
| TX2:188 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common | CLOSED | (y) plain | NGE |
| TX2:189 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1 | CLOSED | (y) plain | NGE |
| TX2:190 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1 | CLOSED | (y) plain | NGE |
| TX2:191 | crates/aspis-statement/src/pool_v1/payment_relation.rs::withdrawal_common | CLOSED | (y) plain | NFY |
| TX2:192 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from | OPEN |  | inherited |
| TX2:193 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot | OPEN |  | inherited |
| TX2:194 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at | OPEN |  | inherited |
| TX2:195 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot | OPEN |  | inherited |
| TX2:196 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at | OPEN |  | inherited |
| TX2:197 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable | OPEN |  | inherited |
| TX2:198 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused | OPEN |  | inherited |
| TX2:199 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable | OPEN |  | inherited |
| TX2:200 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused | OPEN |  | inherited |
| TX2:201 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1 | OPEN |  | inherited |
| TX2:202 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2 | OPEN |  | inherited |
| TX2:203 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1 | OPEN |  | inherited |
| TX2:204 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2 | OPEN |  | inherited |
| TX2:205 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero | OPEN |  | inherited |
| TX2:206 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v1 | OPEN |  | inherited |
| TX2:207 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v2 | OPEN |  | inherited |
| TX2:208 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v1 | OPEN |  | inherited |
| TX2:209 | crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v2 | OPEN |  | inherited |
| TX2:210 | programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest | CLOSED | (y) | NGC |
| TX2:211 | programs/r1-cost-probe/src/lib.rs::error | OPEN |  | inherited |
| TX2:212 | programs/r1-cost-probe/src/lib.rs::observer | OPEN |  | inherited |
| TX2:213 | programs/r1-cost-probe/src/lib.rs::process_r1_cost_probe_instruction | OPEN |  | inherited |
| TX2:214 | programs/r1-cost-probe/src/pool_route.rs::admitted | OPEN |  | inherited |
| TX2:215 | programs/r1-cost-probe/src/r1_pool_adapter.rs::asq8_common | CLOSED | (y) plain | NFY |
| TX2:216 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box | OPEN |  | inherited |
| TX2:217 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release | OPEN |  | inherited |
| TX2:218 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box | OPEN |  | inherited |
| TX2:219 | programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result | CLOSED | (y) plain | NGI |
| TX2:220 | programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id | OPEN |  | inherited |
| TX2:221 | programs/r1-cost-probe/src/r1_pool_adapter.rs::process | OPEN |  | inherited |
| TX2:222 | programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_buffer_meta_ok | CLOSED | (y) plain | NFQ |
| TX2:223 | programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok | OPEN |  | inherited |
| TX2:224 | programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement | CLOSED | (y) plain | NGE |
| TX2:225 | programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id | OPEN |  | inherited |
| TX2:226 | programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer | CLOSED | (y) plain | NGI |
| TX2:227 | programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box | CLOSED | (y) plain | NGE |
| TX2:228 | programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box | CLOSED | (y) plain | NGE |
| TX2:229 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data | OPEN |  | inherited |
| TX2:230 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len | OPEN |  | inherited |
| TX2:231 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key | CLOSED | (y) | NFU |
| TX2:232 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner | CLOSED | (y) | NFU |
| TX2:233 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts | OPEN |  | inherited |
| TX2:234 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry | OPEN |  | inherited |
| TX2:235 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts | OPEN |  | inherited |
| TX2:236 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account | OPEN |  | inherited |
| TX2:237 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer | CLOSED | (y) | NFU |
| TX2:238 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint | OPEN |  | inherited |
| TX2:239 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot | OPEN |  | inherited |
| TX2:240 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2 | OPEN |  | inherited |
| TX2:241 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned | OPEN |  | inherited |
| TX2:242 | programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8 | OPEN |  | inherited |
| TX1:NGB001 | programs/r1-cost-probe/src/lib.rs::error | OPEN |  | NGB OPEN |
| TX1:NGB002 | crates/aspis-core/src/transcript.rs::circle_fallback_point | OPEN |  | NGB OPEN |
| TX1:NGB003 | crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31 | CLOSED | (y) | NHH |
| TX1:NGB004 | crates/aspis-core/src/circle.rs::secure_ood_circle_point_from_parameter | OPEN |  | NGB OPEN |
| TX1:NGB005 | crates/aspis-core/src/r0/scalar.rs::QM31::from_m31 | CLOSED | (y) | NHH |
| TX1:NGB006 | crates/aspis-core/src/circle.rs::secure_circle_point_from_parameter | OPEN |  | NGB OPEN |
| TX1:NGB007 | crates/aspis-core/src/r0/scalar.rs::CM31::from_m31 | CLOSED | (y) | NHH |
| TX1:NGB008 | crates/aspis-core/src/r0/scalar.rs::M31::from_m31 | CLOSED | (y) | NHH |
| TX2:NGB009 | crates/aspis-core/src/r0/scalar.rs::QM31::from_m31 | CLOSED | (y) | NHH |
| TX2:NGB010 | crates/aspis-core/src/r0/scalar.rs::CM31::from_m31 | CLOSED | (y) | NHH |
| TX2:NGB011 | crates/aspis-core/src/field.rs::CM31::from_m31 | CLOSED | (y) | NHH |
| TX2:NGB012 | crates/aspis-core/src/r0/scalar.rs::M31::from_m31 | CLOSED | (y) | NHH |
