# NFU remaining assigned members (live handoff)

Checked new closure: 11 functions / 14 D rows. Driver OPEN. Receipt counts: {'lean': 56, 'kani': 70, 'auditbatch': 2, 'extract': 3}. No new unvalidated row is claimed.

## crates/aspis-r1-cost-probe/src/compact.rs::slot_offset

Rows: TX1:100, TX2:066. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: none.

## crates/aspis-r1-cost-probe/src/compact.rs::expand_semantic

Rows: TX1:098. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: crates/aspis-r1-cost-probe/src/compact.rs::compact_row [D SCC 76]; crates/aspis-r1-cost-probe/src/compact.rs::expand_values [D SCC 77]; crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape [D SCC 78].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::ValidatedRecord<'a>::decode_k

Rows: TX1:147. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: crates/aspis-core/src/field.rs::QM31::from_le_bytes [opaque Q].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record

Rows: TX1:151. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape [D SCC 78]; crates/aspis-r1-cost-probe/src/r1_wire.rs::validate_record_fields [D SCC 181].

## crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record_at

Rows: TX1:152. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: crates/aspis-r1-cost-probe/src/r1_wire.rs::parse_record [D SCC 182]; crates/aspis-r1-cost-probe/src/r1_wire.rs::row_shape [D SCC 78].

## crates/aspis-r1-cost-probe/src/verifier.rs::Accumulator::new

Rows: TX1:174. OPEN callee heap::filled is outside assigned members; see NFU_BOUNDARIES.md. Initialization model/native work cannot promote the caller without this allocation/value/error/frame packet.

Callees: crates/aspis-core/src/r0/heap.rs::filled [D SCC 22]; crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len [D SCC 203].

## crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size

Rows: TX1:187, TX2:112. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len [D SCC 203].

## crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint

Rows: TX1:186. KNE schedule is a retained CLOSED local packet, but the actual reached-call DriverEstablishedDomain must be derived from SAME preparation/query-loop state; preparation is outside NFU and query-loop belongs to NFS. See NFU_BOUNDARIES.md; no free domain hypothesis is admitted.

Callees: crates/aspis-core/src/field.rs::CM31::write_le_bytes [D SCC 2]; crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field.rs::QM31::write_le_bytes [D SCC 7]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag [opaque S]; crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size [D SCC 208]; programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest [D SCC 23].

## crates/aspis-r1-cost-probe/src/verifier.rs::finish_query_dot

Rows: TX2:114. NFG EbyKDot::push is a CLOSED Q callee. Still needs one native iteration on arbitrary pre-state with exact field/weights arguments, full local-record reply/mutation/frame control, Lean loop induction, final new/finish association and caller-established push domains.

Callees: crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::finish [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::new [opaque Q]; crates/aspis-r1-cost-probe/src/fast_pairing.rs::EbyKDot::push [opaque Q]; crates/aspis-r1-cost-probe/src/weights.rs::field [opaque Q].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot

Rows: TX1:343, TX2:239. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: none.

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data

Rows: TX1:335, TX2:229. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: none.

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts

Rows: TX1:339, TX2:235. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key [D SCC 271].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len

Rows: TX1:336, TX2:230. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: none.

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint

Rows: TX1:341, TX2:238. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint_size [D SCC 208]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data_len [D SCC 275]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner [D SCC 276].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned

Rows: TX1:345. Decode/route composition must preserve exact arguments and abort/cleanup order. Transaction callees are outside this assignment; OPEN snapshot/authentication/validation/getter/observer dependencies must be cited, never assumed. No root promotion from a local routing check.

Callees: crates/aspis-r1-cost-probe/src/transport.rs::Variant::tag [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::common [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::semantic_public [D SCC 247]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 [opaque S]; crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 [opaque S]; programs/r1-cost-probe/src/lib.rs::first_decoded [D SCC 267]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts [D SCC 272]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer [D SCC 274]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint [D SCC 277]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_zero [D SCC 278].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1

Rows: TX1:344. Decode/route composition must preserve exact arguments and abort/cleanup order. Transaction callees are outside this assignment; OPEN snapshot/authentication/validation/getter/observer dependencies must be cited, never assumed. No root promotion from a local routing check.

Callees: programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot [D SCC 269]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage1_owned [D SCC 279].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account

Rows: TX2:236. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: programs/r1-cost-probe/src/r1_pool_adapter.rs::readonly_meta_ok [D SCC 286]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::owner [D SCC 276].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry

Rows: TX2:234. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: crates/aspis-statement/src/pool_v1/format.rs::validate_verifier_policy_v1 [D SCC 242]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV1::is_active_at [D SCC 251]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryEntryV2::is_active_at [D SCC 252]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_immutable [D SCC 253]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV1::is_paused [D SCC 254]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_immutable [D SCC 255]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::VerifierRegistryV2::is_paused [D SCC 256]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v1 [D SCC 259]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_entry_v2 [D SCC 261]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v1 [D SCC 263]; crates/aspis-statement/src/pool_v1/verifier_registry.rs::decode_verifier_registry_v2 [D SCC 265]; programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id [D SCC 281]; programs/r1-cost-probe/src/r1_pool_adapter.rs::registry_program_id [D SCC 285]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key [D SCC 271]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account [D SCC 287].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts

Rows: TX2:233. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: crates/aspis-core/src/field.rs::M31::to_le_bytes [opaque S]; crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_checkpoint_box [D SCC 282]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_lane_from_pool_release [D SCC 283]; programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_master_box [D SCC 284]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::key [D SCC 271]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_invariant_release_registry [D SCC 288]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_distinct_accounts [D SCC 272]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_account [D SCC 287]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_readonly_buffer [D SCC 274]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::require_verifier_checkpoint [D SCC 277].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8

Rows: TX2:242. Needs its own frozen native Result/state/frame/ordered-effects packet, matched controls, model association, all callee domains and raw ax2; a CLOSED child alone is insufficient.

Callees: crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier [opaque S]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1 [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter.rs::pool_program_id [D SCC 281]; programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::authenticate_asq8_accounts [D SCC 289].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned

Rows: TX2:241. Decode/route composition must preserve exact arguments and abort/cleanup order. Transaction callees are outside this assignment; OPEN snapshot/authentication/validation/getter/observer dependencies must be cited, never assumed. No root promotion from a local routing check.

Callees: crates/aspis-r1-cost-probe/src/candidate.rs::tx2_authenticated [D SCC 240]; crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1 [opaque S]; programs/r1-cost-probe/src/lib.rs::observer [D SCC 266]; programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result [opaque S]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::OwnedAccount::data [D SCC 270]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::validate_asq8 [D SCC 290].

## programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2

Rows: TX2:240. Decode/route composition must preserve exact arguments and abort/cleanup order. Transaction callees are outside this assignment; OPEN snapshot/authentication/validation/getter/observer dependencies must be cited, never assumed. No root promotion from a local routing check.

Callees: crates/aspis-core/src/r0/domain.rs::FibreIndex::get [opaque Q]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::snapshot [D SCC 269]; programs/r1-cost-probe/src/r1_pool_adapter_owned.rs::stage2_owned [D SCC 291].
