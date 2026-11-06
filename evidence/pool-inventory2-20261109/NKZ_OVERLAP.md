# Overlap with ledger19

Target not yet established. 397 conservative ON source occurrences; 119 match frozen bodies in 183 of the 599 TX rows. 278 are outside that basis. 3 OFF owner rows are numbered separately and excluded from those totals. A body match imports neither a Pool caller-domain proof nor a deployed-feature/model association. Status means composed **conditional** row on its original domain and retained trust.

The three historical Pool helper certificates are retained separately in NKZ_HELPER_REUSE.json; they are outside the 599 and are not counted as newly proved rows. ZERO production Pool closure or promotion is granted. No frozen-body hash disagreements for shared keys.

| Pool occurrence | Frozen function | Existing rows and ledger19 status |
|---|---|---|
| POOL:016 | `crates/aspis-core/src/field.rs::CM31::add` | TX1:001 CLOSED, TX2:001 CLOSED |
| POOL:017 | `crates/aspis-core/src/field.rs::CM31::double` | TX1:002 CLOSED, TX2:002 CLOSED |
| POOL:018 | `crates/aspis-core/src/field.rs::CM31::from_m31` | TX1:004 CLOSED, TX2:NGB011 CLOSED |
| POOL:020 | `crates/aspis-core/src/field.rs::CM31::inv` | TX1:005 CLOSED |
| POOL:021 | `crates/aspis-core/src/field.rs::CM31::inv_with` | TX1:006 CLOSED |
| POOL:023 | `crates/aspis-core/src/field.rs::CM31::mul` | TX1:007 CLOSED, TX2:004 CLOSED |
| POOL:024 | `crates/aspis-core/src/field.rs::CM31::neg` | TX1:009 CLOSED |
| POOL:025 | `crates/aspis-core/src/field.rs::CM31::new` | TX1:010 CLOSED, TX2:006 CLOSED |
| POOL:027 | `crates/aspis-core/src/field.rs::CM31::square` | TX1:011 CLOSED |
| POOL:028 | `crates/aspis-core/src/field.rs::CM31::sub` | TX1:012 CLOSED, TX2:007 CLOSED |
| POOL:029 | `crates/aspis-core/src/field.rs::M31::add` | TX1:013 CLOSED, TX2:009 CLOSED |
| POOL:030 | `crates/aspis-core/src/field.rs::M31::double` | TX1:014 CLOSED, TX2:010 CLOSED |
| POOL:031 | `crates/aspis-core/src/field.rs::M31::from_le_bytes` | TX1:015 CLOSED, TX2:011 CLOSED |
| POOL:034 | `crates/aspis-core/src/field.rs::M31::mul` | TX1:017 CLOSED, TX2:013 CLOSED |
| POOL:035 | `crates/aspis-core/src/field.rs::M31::neg` | TX1:018 CLOSED |
| POOL:037 | `crates/aspis-core/src/field.rs::M31::reduce_u62` | TX1:019 CLOSED |
| POOL:038 | `crates/aspis-core/src/field.rs::M31::reduce_u64` | TX1:020 CLOSED, TX2:014 CLOSED |
| POOL:039 | `crates/aspis-core/src/field.rs::M31::sub` | TX1:021 CLOSED, TX2:015 CLOSED |
| POOL:040 | `crates/aspis-core/src/field.rs::M31::to_le_bytes` | TX1:022 CLOSED, TX2:016 CLOSED |
| POOL:044 | `crates/aspis-core/src/field.rs::PreparedQm31Multiplier::new` | TX1:023 CLOSED |
| POOL:045 | `crates/aspis-core/src/field.rs::QM31::add` | TX1:024 CLOSED, TX2:017 CLOSED |
| POOL:046 | `crates/aspis-core/src/field.rs::QM31::from_cm31` | TX1:025 CLOSED, TX2:018 CLOSED |
| POOL:048 | `crates/aspis-core/src/field.rs::QM31::is_zero` | TX1:028 CLOSED |
| POOL:049 | `crates/aspis-core/src/field.rs::QM31::mul` | TX1:029 CLOSED, TX2:020 CLOSED |
| POOL:050 | `crates/aspis-core/src/field.rs::QM31::neg` | TX1:031 CLOSED |
| POOL:051 | `crates/aspis-core/src/field.rs::QM31::square` | TX1:032 CLOSED, TX2:022 CLOSED |
| POOL:052 | `crates/aspis-core/src/field.rs::QM31::sub` | TX1:033 CLOSED, TX2:023 CLOSED |
| POOL:053 | `crates/aspis-core/src/field.rs::QM31::try_inv` | TX1:034 CLOSED |
| POOL:054 | `crates/aspis-core/src/field.rs::mul_by_r` | TX1:035 CLOSED, TX2:025 CLOSED |
| POOL:055 | `crates/aspis-core/src/field.rs::qm31_from_karatsuba_channel_sums` | TX1:037 CLOSED |
| POOL:059 | `crates/aspis-core/src/field.rs::reduce_u64` | TX1:045 CLOSED, TX2:026 CLOSED |
| POOL:060 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::add` | TX1:047 CLOSED, TX2:028 CLOSED |
| POOL:061 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::c0` | TX2:029 CLOSED |
| POOL:062 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::c1` | TX2:030 CLOSED |
| POOL:063 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::from_qm31` | TX1:050 CLOSED, TX2:033 CLOSED |
| POOL:064 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::mul` | TX1:051 CLOSED, TX2:034 CLOSED |
| POOL:065 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::neg` | TX1:054 CLOSED |
| POOL:066 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::new` | TX1:055 CLOSED, TX2:037 CLOSED |
| POOL:067 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::sub` | TX1:057 CLOSED, TX2:038 CLOSED |
| POOL:068 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes` | TX1:058 CLOSED, TX2:039 CLOSED |
| POOL:069 | `crates/aspis-core/src/field/wide_exact.rs::WideExact::to_limbs` | TX1:059 CLOSED, TX2:040 CLOSED |
| POOL:071 | `crates/aspis-core/src/field/wide_exact.rs::canonical_qm31` | TX1:060 CLOSED, TX2:041 CLOSED |
| POOL:072 | `crates/aspis-core/src/field/wide_exact.rs::mul_u` | TX1:061 CLOSED, TX2:042 CLOSED |
| POOL:090 | `crates/aspis-core/src/r0/merkle.rs::parent_with_digest` | TX1:065 CLOSED |
| POOL:099 | `crates/aspis-core/src/r0/scalar.rs::CM31::from_m31` | TX1:NGB007 CLOSED, TX2:NGB010 CLOSED |
| POOL:101 | `crates/aspis-core/src/r0/scalar.rs::M31::from_m31` | TX1:NGB008 CLOSED, TX2:NGB012 CLOSED |
| POOL:103 | `crates/aspis-core/src/r0/scalar.rs::QM31::from_m31` | TX1:NGB005 CLOSED, TX2:NGB009 CLOSED |
| POOL:105 | `crates/aspis-core/src/r0/scalar.rs::WideExact::from_m31` | TX2:046 CLOSED, TX1:NGB003 CLOSED |
| POOL:151 | `crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical` | TX1:198 CLOSED, TX2:146 CLOSED |
| POOL:152 | `crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical` | TX1:199 CLOSED, TX2:147 CLOSED |
| POOL:153 | `crates/aspis-statement/src/atomic_statement.rs::unwrap_fixed_slice` | TX1:200 CLOSED, TX2:148 CLOSED |
| POOL:161 | `crates/aspis-statement/src/pool_v1/format.rs::decode_pool_identity_v1` | TX2:149 CLOSED |
| POOL:162 | `crates/aspis-statement/src/pool_v1/format.rs::decode_verifier_policy_v1` | TX2:150 CLOSED |
| POOL:166 | `crates/aspis-statement/src/pool_v1/format.rs::pool_v1_tree_parent` | TX1:201 CLOSED |
| POOL:167 | `crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1` | TX2:151 CLOSED |
| POOL:170 | `crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::default` | TX1:202 CLOSED |
| POOL:171 | `crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::empty` | TX1:203 CLOSED |
| POOL:183 | `crates/aspis-statement/src/pool_v1/incremental_merkle.rs::pool_v1_empty_roots` | TX1:204 CLOSED |
| POOL:190 | `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_checkpoint_v1` | TX2:152 CLOSED |
| POOL:192 | `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::decode_pool_v1_pair_forest_master_v1` | TX2:153 CLOSED |
| POOL:193 | `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical` | TX1:205 CLOSED, TX2:154 CLOSED |
| POOL:197 | `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte` | TX1:206 CLOSED, TX2:155 CLOSED |
| POOL:200 | `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1` | TX1:207 CLOSED, TX2:156 CLOSED |
| POOL:201 | `crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::validate_master` | TX2:157 CLOSED |
| POOL:202 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier` | TX2:158 CLOSED |
| POOL:203 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind` | TX2:159 CLOSED |
| POOL:204 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common` | TX1:267 CLOSED, TX2:160 CLOSED |
| POOL:205 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier` | TX2:161 CLOSED |
| POOL:206 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::transition_kind` | TX2:162 CLOSED |
| POOL:207 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1` | TX2:163 CLOSED |
| POOL:210 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1` | TX2:164 CLOSED |
| POOL:211 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::statement_public_common` | TX1:274 CLOSED, TX2:166 CLOSED |
| POOL:212 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind` | TX1:275 CLOSED, TX2:167 CLOSED |
| POOL:213 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1` | TX2:168 CLOSED |
| POOL:214 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1` | TX1:276 CLOSED, TX2:169 CLOSED |
| POOL:215 | `crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_result` | TX2:170 CLOSED |
| POOL:216 | `crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1` | TX1:277 CLOSED, TX2:171 CLOSED |
| POOL:217 | `crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1` | TX1:278 CLOSED, TX2:172 CLOSED |
| POOL:218 | `crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact` | TX1:279 CLOSED, TX2:173 CLOSED |
| POOL:219 | `crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate` | TX1:280 CLOSED, TX2:174 CLOSED |
| POOL:224 | `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical` | TX1:285 CLOSED, TX2:175 CLOSED |
| POOL:225 | `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1` | TX1:286 CLOSED, TX2:176 CLOSED |
| POOL:226 | `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1` | TX1:287 CLOSED, TX2:177 CLOSED |
| POOL:227 | `crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1` | TX1:288 CLOSED, TX2:178 CLOSED |
| POOL:228 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common` | TX1:289 CLOSED, TX2:179 CLOSED |
| POOL:229 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1` | TX1:290 CLOSED, TX2:180 CLOSED |
| POOL:230 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1` | TX1:291 CLOSED, TX2:181 CLOSED |
| POOL:231 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::digest_is_canonical` | TX1:292 CLOSED, TX2:182 CLOSED |
| POOL:232 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common` | TX1:293 CLOSED, TX2:183 CLOSED |
| POOL:233 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1` | TX1:294 CLOSED, TX2:184 CLOSED |
| POOL:234 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1` | TX1:295 CLOSED, TX2:185 CLOSED |
| POOL:235 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::require_header` | TX1:296 CLOSED, TX2:186 CLOSED |
| POOL:236 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::transfer_common` | TX1:297 CLOSED, TX2:187 CLOSED |
| POOL:237 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common` | TX1:298 CLOSED, TX2:188 CLOSED |
| POOL:238 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1` | TX1:299 CLOSED, TX2:189 CLOSED |
| POOL:239 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1` | TX1:300 CLOSED, TX2:190 CLOSED |
| POOL:240 | `crates/aspis-statement/src/pool_v1/payment_relation.rs::withdrawal_common` | TX1:301 CLOSED, TX2:191 CLOSED |
| POOL:247 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierEntryStatusV1::try_from` | TX2:192 CLOSED |
| POOL:248 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::has_no_retirement_slot` | TX2:193 CLOSED |
| POOL:249 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::has_no_retirement_slot` | TX2:195 CLOSED |
| POOL:250 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable` | TX2:197 CLOSED |
| POOL:251 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused` | TX2:198 CLOSED |
| POOL:252 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable` | TX2:199 CLOSED |
| POOL:253 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused` | TX2:200 CLOSED |
| POOL:254 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1` | TX2:201 CLOSED |
| POOL:255 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2` | TX2:202 CLOSED |
| POOL:256 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1` | TX2:203 CLOSED |
| POOL:257 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2` | TX2:204 CLOSED |
| POOL:258 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::required_binding_is_zero` | TX2:205 CLOSED |
| POOL:259 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v1` | TX2:206 CLOSED |
| POOL:260 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_entry_v2` | TX2:207 CLOSED |
| POOL:261 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v1` | TX2:208 CLOSED |
| POOL:262 | `crates/aspis-statement/src/pool_v1/verifier_registry.rs::validate_verifier_registry_v2` | TX2:209 CLOSED |
| POOL:263 | `crates/aspis-statement/src/poseidon2.rs::apply_mat4_lazy` | TX1:302 CLOSED |
| POOL:264 | `crates/aspis-statement/src/poseidon2.rs::external_linear_lazy` | TX1:303 CLOSED |
| POOL:267 | `crates/aspis-statement/src/poseidon2.rs::internal_linear_lazy` | TX1:304 CLOSED |
| POOL:268 | `crates/aspis-statement/src/poseidon2.rs::merkle_node_compress_v3` | TX1:305 CLOSED |
| POOL:269 | `crates/aspis-statement/src/poseidon2.rs::permute_optimized_with_trace` | TX1:306 CLOSED |
| POOL:270 | `crates/aspis-statement/src/poseidon2.rs::pow5` | TX1:307 CLOSED |

Overlap statuses are historical evidence, not a fresh theorem replay. Exact obligation hashes, owner modules and evidence paths are in NKZ_INVENTORY.json; full binders remain in the pinned NKN ledger. Conservative alternatives and every corresponding callee are retained.
