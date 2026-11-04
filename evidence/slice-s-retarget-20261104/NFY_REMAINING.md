# Remaining S certificate retargets

**19 rows restored; 70 remain QUALIFIED. S is 27/97 CLOSED and 0/7 headline-coherent roots CLOSED.** All 110 formal/audit slots are charged; no additional prover is authorized by this job.

The replayed 61-module NFY base is clean. The complete certificate-name check finds 125 auxiliary declarations in 69 modules outside that import; their nonreused dependency closure is 92 modules. These are Lean-only retarget/replay obligations. No remaining item needs Kani or extraction. The original native certificates remain historical evidence.

| Auxiliary family | Direct modules | Missing named declarations | Direct affected rows | Other auxiliary families imported |
|---|---:|---:|---:|---|
| NEE | 1 | 1 | 2 | none |
| NEJ | 4 | 4 | 6 | NEE |
| NEL | 4 | 10 | 8 | none |
| NEM | 7 | 21 | 21 | NEJ, NEL |
| NEQ | 8 | 26 | 10 | NBN, NEM |
| NEX | 14 | 27 | 10 | NED |
| NEY | 31 | 36 | 4 | NEX |

Counts overlap across rows. Family-level edges may cycle because a family contains independent layers; the exact module DAG and bottom-up `order` in NFY_AUXILIARY_INPUTS.json are authoritative. Start independent members immediately. Reuse NFY exports and namespace/module maps; successor copies must use their own prefix and never edit NFY files.

Next concrete deliverable: retarget NEQ_ParserCanonical.some_canonical, the NEJ/NEL/NEM arbitrary-prestate frame/receiver laws, and the NEQ/NEX/NEY domain/alignment/Box helpers against NFY. Replay the complete certificate-name inventory, not just the old 88-root aggregate. Then one combined headline/raw/fixture/owner scan and the same selected-callee denial propagation can restore further rows. No row is restored from source compilation alone.

## Remaining occurrences

| Row | Member | Exact remaining obligation |
|---|---|---|
| TX1:198 | crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical | Lean-only retarget/replay: NEQ_ParserCanonical; 0 Kani needed. |
| TX1:199 | crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical | Lean-only retarget/replay: NEL_DigestLoopFrame, NEM_DigestInstance; 0 Kani needed. |
| TX1:205 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical | Lean-only retarget/replay: NEJ_ScannerFramed, NEJ_ScannerWidth; 0 Kani needed. |
| TX1:206 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte | Selected callee remains QUALIFIED: NBP::crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical; 0 Kani needed. |
| TX1:207 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 | Selected callee remains QUALIFIED: NBD::crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical; 0 Kani needed. |
| TX1:269 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_lane_transition_boxed_v1 | Lean-only retarget/replay: NEX_BoxValueExt, NEX_DecoderDomains, NEX_LaneOracle; 0 Kani needed. |
| TX1:270 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_statement_v1 | Lean-only retarget/replay: NEX_DecoderDomains, NEX_StatementExt, NEX_TerminalDomain, NEY_Field00, NEY_Field01, NEY_Field02, NEY_Field03, NEY_Field04, NEY_Field05, NEY_Field06, NEY_Field07, NEY_Field08, NEY_Field09, NEY_Field10, NEY_Field11, NEY_Field12, NEY_Field13, NEY_Field14, NEY_Field15, NEY_Field16, NEY_Field17, NEY_Field18, NEY_Field19, NEY_Field20, NEY_Field21, NEY_Field22, NEY_Field23, NEY_Field24, NEY_Field25, NEY_TerminalGeometry; 0 Kani needed. |
| TX1:271 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_terminal_common_boxed_v1 | Lean-only retarget/replay: NEX_CommonOracle, NEX_DecoderDomains; 0 Kani needed. |
| TX1:272 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_transfer_statement_boxed_v1 | Selected callee remains QUALIFIED: NBP::crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1; 0 Kani needed. |
| TX1:273 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_withdrawal_statement_boxed_v1 | Selected callee remains QUALIFIED: NBP::crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1; 0 Kani needed. |
| TX1:275 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind | Lean-only retarget/replay: NEM_KindInstance; 0 Kani needed. |
| TX1:276 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 | Selected callee remains QUALIFIED: NBP::crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1, NBP::crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1, NBU::crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1; 0 Kani needed. |
| TX1:277 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1 | Lean-only retarget/replay: NEX_AfterDecodeOracle, NEX_AfterstateBox, NEX_DigestCallDomains, NEX_FirstError, NEX_ReadDomains; 0 Kani needed. |
| TX1:278 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 | Lean-only retarget/replay: NEM_EncoderFrame; 0 Kani needed. |
| TX1:280 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate | Lean-only retarget/replay: NEM_FrontierValidatorInstance; 0 Kani needed. |
| TX1:281 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_afterstate_boxed_v1 | Lean-only retarget/replay: NEX_AfterstateBox; 0 Kani needed. |
| TX1:282 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pair_live_snapshot_boxed_v1 | Lean-only retarget/replay: NEX_BoxValueExt, NEX_DecoderDomains, NEX_SnapshotBoxOracle; 0 Kani needed. |
| TX1:283 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_late_public_statement_boxed_v1 | Lean-only retarget/replay: NEX_BoxValueExt, NEX_DecoderDomains, NEX_LateOracle; 0 Kani needed. |
| TX1:284 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::decode_pool_v1_pair_live_snapshot_v1 | Lean-only retarget/replay: NEX_DigestCallDomains, NEX_FirstError, NEX_ReadDomains, NEX_SnapshotParent; 0 Kani needed. |
| TX1:285 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical | Lean-only retarget/replay: NEE_CanonicalFrame, NEJ_ScannerFramed, NEJ_ScannerWidth; 0 Kani needed. |
| TX1:286 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1 | Lean-only retarget/replay: NEM_ArraySnapshotView; 0 Kani needed. |
| TX1:287 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1 | Lean-only retarget/replay: NEM_EncoderFrame; 0 Kani needed. |
| TX1:288 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1 | Lean-only retarget/replay: NEM_FrontierValidatorInstance; 0 Kani needed. |
| TX1:289 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common | Selected callee remains QUALIFIED: NBG::crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common, NBP::crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical; 0 Kani needed. |
| TX1:290 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1 | Lean-only retarget/replay: NEQ_BorrowWidth, NEQ_PaymentDomains; 0 Kani needed. |
| TX1:291 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1 | Lean-only retarget/replay: NEQ_BorrowWidth, NEQ_PaymentDomains; 0 Kani needed. |
| TX1:293 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common | Lean-only retarget/replay: NEJ_CommonSourceFrame, NEJ_WindowStep; 0 Kani needed. |
| TX1:294 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1 | Lean-only retarget/replay: NEM_PaymentFrame; 0 Kani needed. |
| TX1:295 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1 | Lean-only retarget/replay: NEM_PaymentFrame; 0 Kani needed. |
| TX1:298 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common | Lean-only retarget/replay: NEL_CommonOracle; 0 Kani needed. |
| TX1:299 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1 | Lean-only retarget/replay: NEL_CommonOracle, NEL_PaymentFieldCarriers, NEL_PaymentOracle; 0 Kani needed. |
| TX1:300 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1 | Lean-only retarget/replay: NEL_CommonOracle, NEL_PaymentFieldCarriers, NEL_PaymentOracle; 0 Kani needed. |
| TX1:332 | programs/r1-cost-probe/src/r1_pool_adapter.rs::decode_public_statement_box | Lean-only retarget/replay: NEX_StatementExt, NEY_Field00, NEY_Field01, NEY_Field02, NEY_Field03, NEY_Field04, NEY_Field05, NEY_Field06, NEY_Field07, NEY_Field08, NEY_Field09, NEY_Field10, NEY_Field11, NEY_Field12, NEY_Field13, NEY_Field14, NEY_Field15, NEY_Field16, NEY_Field17, NEY_Field18, NEY_Field19, NEY_Field20, NEY_Field21, NEY_Field22, NEY_Field23, NEY_Field24, NEY_Field25; 0 Kani needed. |
| TX2:146 | crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical | Lean-only retarget/replay: NEQ_ParserCanonical; 0 Kani needed. |
| TX2:147 | crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical | Lean-only retarget/replay: NEL_DigestLoopFrame, NEM_DigestInstance; 0 Kani needed. |
| TX2:154 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical | Lean-only retarget/replay: NEJ_ScannerFramed, NEJ_ScannerWidth; 0 Kani needed. |
| TX2:155 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::first_canonical_byte | Selected callee remains QUALIFIED: NBP::crates/aspis-statement/src/atomic_statement.rs::encode_digest_canonical; 0 Kani needed. |
| TX2:156 | crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_output_lane_v1 | Selected callee remains QUALIFIED: NBD::crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::digest_is_canonical; 0 Kani needed. |
| TX2:158 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier | Lean-only retarget/replay: NEQ_NullifierDomains; 0 Kani needed. |
| TX2:159 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind | Lean-only retarget/replay: NEM_KindInstance; 0 Kani needed. |
| TX2:161 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier | Lean-only retarget/replay: NEQ_NullifierDomains; 0 Kani needed. |
| TX2:162 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::transition_kind | Lean-only retarget/replay: NEM_KindInstance; 0 Kani needed. |
| TX2:163 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::decode_pool_v1_pair_forest_terminal_request_v1 | Selected callee remains QUALIFIED: NBD::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind, NBP::crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1, NBP::crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1; 0 Kani needed. |
| TX2:164 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1 | Lean-only retarget/replay: NEY_ReachedResultDomains, NEY_ResultConstants, NEY_ResultProjection, NEY_ResultStores; 0 Kani needed. |
| TX2:165 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1 | Lean-only retarget/replay: NEM_EncoderReceiver, NEM_KindInstance, NEQ_EncoderDomains, NEQ_LateBorrow, NEQ_RootFrame; 0 Kani needed. |
| TX2:167 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind | Lean-only retarget/replay: NEM_KindInstance; 0 Kani needed. |
| TX2:168 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1 | Lean-only retarget/replay: NEY_ReachedResultDomains; 0 Kani needed. |
| TX2:169 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1 | Selected callee remains QUALIFIED: NBP::crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1, NBP::crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1, NBU::crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1; 0 Kani needed. |
| TX2:170 | crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_result | Lean-only retarget/replay: NEQ_ResultValidator; 0 Kani needed. |
| TX2:171 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1 | Lean-only retarget/replay: NEX_AfterDecodeOracle, NEX_AfterstateBox, NEX_DigestCallDomains, NEX_FirstError, NEX_ReadDomains; 0 Kani needed. |
| TX2:172 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1 | Lean-only retarget/replay: NEM_EncoderFrame; 0 Kani needed. |
| TX2:174 | crates/aspis-statement/src/pool_v1/pair_terminal.rs::validate_verified_afterstate | Lean-only retarget/replay: NEM_FrontierValidatorInstance; 0 Kani needed. |
| TX2:175 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::digest_is_canonical | Lean-only retarget/replay: NEE_CanonicalFrame, NEJ_ScannerFramed, NEJ_ScannerWidth; 0 Kani needed. |
| TX2:176 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1 | Lean-only retarget/replay: NEM_ArraySnapshotView; 0 Kani needed. |
| TX2:177 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_live_snapshot_v1 | Lean-only retarget/replay: NEM_EncoderFrame; 0 Kani needed. |
| TX2:178 | crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::validate_pool_v1_pair_live_snapshot_v1 | Lean-only retarget/replay: NEM_FrontierValidatorInstance; 0 Kani needed. |
| TX2:179 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_common | Selected callee remains QUALIFIED: NBG::crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common, NBP::crates/aspis-statement/src/atomic_statement.rs::decode_digest_canonical; 0 Kani needed. |
| TX2:180 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_private_transfer_public_v1 | Lean-only retarget/replay: NEQ_BorrowWidth, NEQ_PaymentDomains; 0 Kani needed. |
| TX2:181 | crates/aspis-statement/src/pool_v1/payment_relation.rs::decode_pool_v1_withdrawal_public_v1 | Lean-only retarget/replay: NEQ_BorrowWidth, NEQ_PaymentDomains; 0 Kani needed. |
| TX2:183 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_common | Lean-only retarget/replay: NEJ_CommonSourceFrame, NEJ_WindowStep; 0 Kani needed. |
| TX2:184 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_private_transfer_public_v1 | Lean-only retarget/replay: NEM_PaymentFrame; 0 Kani needed. |
| TX2:185 | crates/aspis-statement/src/pool_v1/payment_relation.rs::encode_pool_v1_withdrawal_public_v1 | Lean-only retarget/replay: NEM_PaymentFrame; 0 Kani needed. |
| TX2:188 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_common | Lean-only retarget/replay: NEL_CommonOracle; 0 Kani needed. |
| TX2:189 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_private_transfer_public_v1 | Lean-only retarget/replay: NEL_CommonOracle, NEL_PaymentFieldCarriers, NEL_PaymentOracle; 0 Kani needed. |
| TX2:190 | crates/aspis-statement/src/pool_v1/payment_relation.rs::validate_pool_v1_withdrawal_public_v1 | Lean-only retarget/replay: NEL_CommonOracle, NEL_PaymentFieldCarriers, NEL_PaymentOracle; 0 Kani needed. |
| TX2:219 | programs/r1-cost-probe/src/r1_pool_adapter.rs::emit_result | Selected callee remains QUALIFIED: NBD::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind, NBU::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::nullifier, NBU::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind, NBU::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::nullifier, NBU::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalStatementV1::transition_kind, NEY::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_result_v1, NEY::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_result_against_statement_v1; 0 Kani needed. |
| TX2:224 | programs/r1-cost-probe/src/r1_pool_adapter.rs::reconstruct_asq8_statement | Selected callee remains QUALIFIED: NEU::programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box, NEU::programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box; 0 Kani needed. |
| TX2:226 | programs/r1-cost-probe/src/r1_pool_adapter.rs::scan_proof_buffer | Selected callee remains QUALIFIED: NBU::crates/aspis-statement/src/pool_v1/pair_terminal.rs::decode_pool_v1_pair_verified_afterstate_v1, NBU::crates/aspis-statement/src/pool_v1/pair_terminal.rs::encode_pool_v1_pair_verified_afterstate_v1; 0 Kani needed. |
| TX2:227 | programs/r1-cost-probe/src/r1_pool_adapter.rs::transfer_statement_box | Selected callee remains QUALIFIED: NBU::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1; 0 Kani needed. |
| TX2:228 | programs/r1-cost-probe/src/r1_pool_adapter.rs::withdrawal_statement_box | Selected callee remains QUALIFIED: NBU::crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::validate_pool_v1_pair_forest_terminal_statement_v1; 0 Kani needed. |

Outside this job: D driver roots and incoming Prepared/powers/prepare domains; Pool same-instruction/program-id/carrier/account/settlement association; L159/L181 concrete realization; L187 cold coherent closure replay; L188 final trust/source/artifact audit. The two NFX inventory defects remain OPEN on this branch. Parallel workers own their repairs. RuntimePersistence, RuntimeReturnData (nonempty 1..1024), RuntimeMemcmp and P6/D188 option-A transport are retained.
