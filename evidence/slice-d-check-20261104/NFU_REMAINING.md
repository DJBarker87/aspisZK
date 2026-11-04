# NFU remaining assigned/context members

Admitted: 11 new functions / 14 new D rows; D 35/343 CLOSED, 308 OPEN. Driver OPEN. Budget charged {'kani': 100, 'lean_support': 60, 'extraction': 3} of 100 Kani/60 Lean-support/3 extraction. Receipt-only fragments have no closure credit.

## crates/aspis-r1-cost-probe/src/compact.rs::slot_offset

Rows TX1:100, TX2:066. Independent small helper still needs full native all-offset/row Result and overflow/error/frame certificate plus canonical model port. No prior horizontal packet was reclassified as closure. Needs fresh Kani and Lean/audit budget.

Real callees: none.

## crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic

Rows TX1:098. K042/K043 cover only invalid semantic/output lengths. Valid path still needs the exact original-row iteration schedule, expand_values SAME output-window domain, expansion offsets/frame/disjointness and canonical source/model induction. The CLOSED expand_values child does not close this caller. Needs native schedule and model/audit work.

Real callees: crates/aspis-r1-cost-probe/src/compact.rs::compact_row [D SCC 76]; crates/aspis-r1-cost-probe/src/compact.rs::expand_values [D SCC 77]; crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape [D SCC 78].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k

Rows TX1:147. Needs exact ValidatedRecord row/framed caller-established domain, original payload windows, N=1/28/29 canonical field decoding, all errors and returned array/frame association. Getter closure is insufficient. Needs native decoder and Lean/substitution/audit budget.

Real callees: crates/aspis-core/src/field.rs::QM31::from_le_bytes [opaque Q].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record

Rows TX1:151. K044..049 give invalid-row/length/tag guard pairs; K015/K063 isolate bad-header return with assert-false unreachable validator. Valid-header path, borrowed token provenance, complete exact errors and validate_record_fields substitution remain OPEN. E001 is a reduced-carrier reference only (NFU_REFERENCE_CARRIER_FINDING.md). Needs native valid branch plus full-error model transport/audit.

Real callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape [D SCC 78]; crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields [D SCC 181].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record_at

Rows TX1:152. K021/K053 prove short-get returns before parser. Long-get path needs checked add/get and SAME original slice/result/error forwarding through parse_record. E002 extraction is reduced-carrier only. Needs native caller valid branch and parser packet/model association; no full-buffer replay.

Real callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record [D SCC 182]; crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape [D SCC 78].

## crates/aspis-r1-cost-probe/src/verifier.rs::Accumulator::new

Rows TX1:174. Accumulator::new TX1:174 depends on OPEN heap::filled outside this assignment; no allocation/value/error/frame packet exists. Record this slice-boundary obligation before any caller closure (NFU_BOUNDARIES.md). Requires that external native/Lean packet and native initialization/model join.

Real callees: crates/aspis-core/src/r0/heap.rs::filled [D SCC 22]; crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len [D SCC 203].

## crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size

Already CLOSED in baseline; no duplicate NFU credit. Rows TX1:187, TX2:112.

## crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint

Rows TX1:186. KNE 116-transition schedule/native_result is reusable but DriverEstablishedDomain is not proved at this call site: SAME p/a preparation provenance, S2, weights64,22 indices<262144, canonical fields and a.next=10. Preparation is outside NFU, query loop belongs to NFS, field writers to NFT. Need exact incoming-state domain derivation plus all remaining real callee packets; no free accepted-run hypothesis.

Real callees: crates/aspis-core/src/field.rs::CM31::write_le_bytes [D SCC 2]; crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field.rs::QM31::write_le_bytes [D SCC 7]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag [opaque S]; crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size [D SCC 208]; programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot

Rows TX2:114. K072/K073 and the remaining finish_g observation pairs are a typed arbitrary-prestate one-step candidate with unconstrained push reply/nine-word receiver mutation; see NFU_FINISH_CANDIDATE.json. NFG push is CLOSED on canonical E/valid receiver and arbitrary raw scalar/count. Still needs frozen source-erasure/typed-cohort transport without legacy FIo, one loop induction with abort prefixes, new/finish association and final aggregate bounds/caller domain. E003 does not prove those joins. Requires additional native association and Lean/audit budget.

Real callees: crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot

Rows TX1:343, TX2:239. Needs actual account data borrow/length/owner/key/errors, exact byte copy and full Vec allocation/cleanup/frame/provenance. Existing source dependencies and copy/fidelity shapes are not assumed; needs one-window KMX controls/Lean frame composition and full record/error model.

Real callees: none.

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data

Rows TX1:335, TX2:229. Needs complete actual borrowed data Result/lifetime/provenance and all error variants with canonical emitted model association; native pointer/error packet and Lean/audit still required.

Real callees: none.

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts

Rows TX1:339, TX2:235. Needs SAME account-key identity/byte comparison arguments, all duplicate-position/first-error paths and runtime memcmp accepted-trust interface, with native local-record packet and Lean source-order composition.

Real callees: programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key [D SCC 271].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len

Rows TX1:336, TX2:230. K099/K100 are the planned native all-usize Ok/error discrimination pair (check receipts for completion), never a composed claim. Full emitted Result error-carrier/clone correspondence and model/audit support remain OPEN; native evidence alone is insufficient.

Real callees: none.

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint

Rows TX1:341, TX2:238. K051 is the planned exact owner/metadata/deferred-length Result diagnostic (check receipt for completion), without a matched control, never a composed claim. Full emitted clone/error carrier and Pubkey equality/accepted runtime memcmp interface association, data_len domain and complete raw audit remain OPEN.

Real callees: crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size [D SCC 208]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len [D SCC 275]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner [D SCC 276].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned

Rows TX1:345. K056/K057 only empty-account rejection. OPEN snapshot/data/metadata/authentication dependencies plus exact route, original arguments, return/error, observer and cleanup order prevent composed closure. Needs native schedule/model joins without assuming successful tx1.

Real callees: crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public [D SCC 247]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 [opaque S]; crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 [opaque S]; programs/r1-cost-probe/src/lib.rs::first_decoded [D SCC 267]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts [D SCC 272]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer [D SCC 274]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint [D SCC 277]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero [D SCC 278].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1

Rows TX1:344. K054/K055 only empty-account rejection. Full decode/route argument preservation, observer deployed None rename pair under (ae), transaction result/error forwarding and abort/cleanup order remain OPEN. Transaction bodies are excluded from this assignment; cite only CLOSED packets. Needs caller native schedule and model joins.

Real callees: programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot [D SCC 269]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned [D SCC 279].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account

Rows TX2:236. Needs exact account owner/key/flags domain, original metadata arguments and complete Result/error/frame model; can cite CLOSED key/owner/read-only helpers only at their established call domains. Needs native caller and Lean/audit work.

Real callees: programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok [D SCC 286]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner [D SCC 276].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry

Rows TX2:234. Needs exact account order/owner/key/data borrow, registry decode and accepted authentication comparison interfaces, all abort/cleanup prefixes. OPEN data/snapshot/authentication children and out-of-assignment dependencies are not assumed; needs their packets plus caller native/model certificate.

Real callees: crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1 [D SCC 242]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at [D SCC 251]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at [D SCC 252]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable [D SCC 253]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused [D SCC 254]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable [D SCC 255]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused [D SCC 256]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1 [D SCC 259]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2 [D SCC 261]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1 [D SCC 263]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2 [D SCC 265]; programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id [D SCC 281]; programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id [D SCC 285]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key [D SCC 271]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account [D SCC 287].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts

Rows TX2:233. Needs exact SAME account order/data, authentication result and all first-error/cleanup prefixes, with OPEN snapshot/data/registry/validate children instantiated. Needs real callee closure and caller native/model certificate.

Real callees: crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box [D SCC 282]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release [D SCC 283]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box [D SCC 284]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key [D SCC 271]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry [D SCC 288]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts [D SCC 272]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account [D SCC 287]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer [D SCC 274]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint [D SCC 277].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8

Rows TX2:242. Needs exact statement/ASQ8 payload decoder domain and same account provenance/first-error Result plus all outside-assignment child packets. Needs local native record oracle, one-window/loop composition where applicable and canonical model/audit.

Real callees: crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1 [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id [D SCC 281]; programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts [D SCC 289].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned

Rows TX2:241. K060/K061 only empty-account rejection. OPEN account authentication/snapshot/validate/checkpoint dependencies and full route/error/cleanup order prevent closure; needs actual caller packet and model/audit, not transaction-body ownership.

Real callees: crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated [D SCC 240]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1 [opaque S]; programs/r1-cost-probe/src/lib.rs::observer [D SCC 266]; programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8 [D SCC 290].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2

Rows TX2:240. K058/K059 only empty-account rejection. Full decode/route, SAME checkpoint/statement/proof arguments and exact tx2 result/error/cleanup require child packets, observer None controls and canonical model association; tx2 itself excluded.

Real callees: crates/aspis-core/src/r0/domain.rs::FibreIndex::get [opaque Q]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot [D SCC 269]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned [D SCC 291].

No unused proof budget remains once NFU_RECEIPTS_CHECK.json passes. The outstanding model/domain/induction/audit obligations are recorded above rather than characterized as Kani-only blockers. No root or 100-bit per-attempt claim is established.
