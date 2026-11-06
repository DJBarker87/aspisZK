# New Pool difference from NKS_

Target not yet established. Scope reduction only; no proof, status promotion, trust change or ledger edit.

Old freeze4bb3b3f5 / ELF121f3e29…; new Pool freeze b936275465600469312d1f058cdc91ea2a11f3dc / ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc. Crates remain4bb3b3f5. Same NKS_/NGB_ method and conservative alternatives; only source/compiler pins, removed-root handling and reports retargeted. NKZ_DIFF.json lists every removed row and old/new retained ID.

| Count | NKS | NKZ | Removed |
|---|---:|---:|---:|
| ON source occurrences | 613 | 397 | 216 |
| New to599-row basis | 494 | 278 | 216 |
| Shared body occurrences | 119 | 119 | 0 |
| Basis rows matched | 183 | 183 | 0 |
| New class A | 171 | 113 | 58 |
| New class B | 235 | 124 | 111 |
| New class C | 31 | 11 | 20 |
| New class D | 57 | 30 | 27 |

All397 retained functions have the same class.396 retained bodies are byte-identical; only processor::process_instruction changes (seven legacy arms removed). No function is added to the ON closure. Removed rows are listed below; none is labelled CLOSED by deletion.

Seven removed dispatch alternatives: ASIN (old OFF), ASDI/ASPT/ASWD/ASPP/ASPF/ASPX (old ON). Seven source alternatives remain: AS8C/AS8D/ASQ8 ON; AS8I and cfg-disabled ASF8/ASJP/ASJW OFF. No prepared/cancel/settle legacy root remains, and there is no standalone admin/registry/close instruction.

| Original exclusive guard owner | Old row / scope | New disposition |
|---|---|---|
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1` | POOL:412 ON_CONSERVATIVE_CLOSURE | POOL:328 ON_CONSERVATIVE_CLOSURE OPEN |
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1` | POOL:414 ON_CONSERVATIVE_CLOSURE | POOL:330 ON_CONSERVATIVE_CLOSURE OPEN |
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1` | POOL:614 OFF_REVIEW_NOT_ON_CLOSURE | POOL:398 OFF_REVIEW_NOT_ON_CLOSURE OPEN |
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1` | POOL:411 ON_CONSERVATIVE_CLOSURE | POOL:327 ON_CONSERVATIVE_CLOSURE OPEN |
| `programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1` | POOL:615 OFF_REVIEW_NOT_ON_CLOSURE | POOL:399 OFF_REVIEW_NOT_ON_CLOSURE OPEN |
| `programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1` | POOL:616 OFF_REVIEW_NOT_ON_CLOSURE | POOL:400 OFF_REVIEW_NOT_ON_CLOSURE OPEN |
| `programs/aspis-pool/src/processor.rs::close_program_account_v1` | POOL:492 ON_CONSERVATIVE_CLOSURE | REMOVED SOURCE |
| `programs/aspis-pool/src/processor.rs::process_prepare_settlement_with_runtime_v1` | POOL:514 ON_CONSERVATIVE_CLOSURE | REMOVED SOURCE |
| `programs/aspis-pool/src/processor.rs::process_settle_prepared_with_runtime_v1` | POOL:516 ON_CONSERVATIVE_CLOSURE | REMOVED SOURCE |
| `programs/aspis-pool/src/processor.rs::create_and_write_marker_v1` | POOL:493 ON_CONSERVATIVE_CLOSURE | REMOVED SOURCE |
| `programs/aspis-pool/src/processor.rs::process_withdrawal_with_runtime_v1` | POOL:517 ON_CONSERVATIVE_CLOSURE | REMOVED SOURCE |
| `programs/aspis-pool/src/transition.rs::initialize_pool_accounts_v1` | POOL:617 OFF_REVIEW_NOT_ON_CLOSURE | REMOVED SOURCE |
| `programs/aspis-pool/src/transition.rs::apply_authorized_append_after_checked_state_v1` | POOL:571 ON_CONSERVATIVE_CLOSURE | REMOVED SOURCE |

13→6 original guard owners:7 removed,3 ON and3 OFF retained;0 newly proved.

| Held CPI/callback owner | Old row / scope | New disposition |
|---|---|---|
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1` | POOL:412 ON_CONSERVATIVE_CLOSURE | POOL:328 ON_CONSERVATIVE_CLOSURE OPEN |
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1` | POOL:414 ON_CONSERVATIVE_CLOSURE | POOL:330 ON_CONSERVATIVE_CLOSURE OPEN |
| `programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1` | POOL:616 OFF_REVIEW_NOT_ON_CLOSURE | POOL:400 OFF_REVIEW_NOT_ON_CLOSURE OPEN |
| `programs/aspis-pool/src/transition.rs::apply_authorized_append_after_checked_state_v1` | POOL:571 ON_CONSERVATIVE_CLOSURE | REMOVED SOURCE |

Four held sites→three: legacy transition before_persist callback removed; pair deposit and terminal stay ON; cfg-disabled pair withdrawal stays OFF. RuntimeCpiReadonlyEntry7 remains pending and unused. Accessor sites21→15; all seven data_is_empty source sites remain, so the K086 nullifier-classifier family is not removed. Its native production reachability/exclusion remains UNPROVED (liveness/abort).

Revised estimate (not a measurement): A/B/C248 rows at the successful predecessor-helper sensitivity of1–2 rows/job gives124–248 predecessor-sized job-slots (was219–437 for437 rows). This is not established driver throughput; no finite empirical upper bound. D30 rows (was57) retain separate unbounded uncertainty. The surviving prefix-to-CPI and P1..P4 producers remain OPEN; removal does not decide owner option A/B.

| Removed ON occurrence | Class | Frozen function |
|---|---|---|
| POOL:079 | B | `crates/aspis-core/src/r0/basis.rs::NaturalBasis::apply` |
| POOL:081 | B | `crates/aspis-core/src/r0/basis.rs::NaturalBasis::transpose` |
| POOL:162 | B | `crates/aspis-statement/src/pool_v1/authorization_receipt.rs::decode_pool_v1_authorization_receipt_v1` |
| POOL:163 | A | `crates/aspis-statement/src/pool_v1/authorization_receipt.rs::receipt_digest_v1` |
| POOL:164 | B | `crates/aspis-statement/src/pool_v1/authorization_receipt.rs::validate_pool_v1_authorization_receipt_for_settlement_v1` |
| POOL:166 | A | `crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs::PoolV1AuthorizationReceiptAccountV1::pda_inputs` |
| POOL:167 | C | `crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs::decode_pool_v1_authorization_receipt_account_v1` |
| POOL:168 | B | `crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs::pool_v1_authorization_receipt_binding_digest_v1` |
| POOL:169 | B | `crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs::pool_v1_authorization_receipt_pda_inputs_for_binding_v1` |
| POOL:170 | B | `crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs::pool_v1_authorization_receipt_request_digest_v1` |
| POOL:171 | B | `crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs::validate_pool_v1_authorization_receipt_account_pda_inputs_v1` |
| POOL:172 | B | `crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs::validate_pool_v1_authorization_receipt_account_request_v1` |
| POOL:173 | A | `crates/aspis-statement/src/pool_v1/authorization_receipt_account.rs::wrapper_digest_v1` |
| POOL:174 | A | `crates/aspis-statement/src/pool_v1/deposit.rs::digest_is_canonical` |
| POOL:175 | B | `crates/aspis-statement/src/pool_v1/deposit.rs::encode_deposit_receipt_v1` |
| POOL:176 | B | `crates/aspis-statement/src/pool_v1/deposit.rs::validate_deposit_event_v1` |
| POOL:177 | B | `crates/aspis-statement/src/pool_v1/deposit.rs::validate_deposit_receipt_v1` |
| POOL:185 | B | `crates/aspis-statement/src/pool_v1/historical_anchor.rs::PoolV1TransitionKind::decode` |
| POOL:186 | B | `crates/aspis-statement/src/pool_v1/historical_anchor.rs::decode_historical_anchor_envelope_v1` |
| POOL:187 | A | `crates/aspis-statement/src/pool_v1/historical_anchor.rs::digest_is_canonical` |
| POOL:188 | B | `crates/aspis-statement/src/pool_v1/historical_anchor.rs::encode_historical_anchor_envelope_v1` |
| POOL:189 | B | `crates/aspis-statement/src/pool_v1/historical_anchor.rs::validate_historical_anchor_envelope_v1` |
| POOL:191 | B | `crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::append_two_with_empty_roots` |
| POOL:198 | B | `crates/aspis-statement/src/pool_v1/incremental_merkle.rs::IncrementalMerkleTreeV1::validate_terminal_root_against_history_with_empty_roots` |
| POOL:202 | B | `crates/aspis-statement/src/pool_v1/incremental_merkle.rs::ValidatedIncrementalMerkleTreeV1<'a>::append_two` |
| POOL:210 | A | `crates/aspis-statement/src/pool_v1/nullifier_marker.rs::PoolV1NullifierMarkerV1::from_historical_anchor` |
| POOL:273 | C | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::decode_binding_fields` |
| POOL:274 | B | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::decode_transition_kind` |
| POOL:275 | B | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::decode_verifier_dispatch_result_v1` |
| POOL:276 | A | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::digest_is_canonical` |
| POOL:277 | B | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::encode_binding_fields` |
| POOL:278 | B | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::encode_verifier_dispatch_request_v1` |
| POOL:279 | B | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::encode_verifier_dispatch_result_v1` |
| POOL:280 | B | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::historical_anchor_envelope_digest_v1` |
| POOL:281 | B | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::validate_verifier_dispatch_binding_v1` |
| POOL:282 | B | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::verifier_dispatch_binding_from_envelope_v1` |
| POOL:283 | A | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::verifier_proof_body_digest_v1` |
| POOL:284 | B | `crates/aspis-statement/src/pool_v1/verifier_dispatch.rs::verifier_statement_payload_digest_v1` |
| POOL:315 | A | `programs/aspis-pool/src/anchor.rs::PrevalidatedHistoricalAnchorV1::authenticated` |
| POOL:316 | A | `programs/aspis-pool/src/anchor.rs::PrevalidatedHistoricalAnchorV1::header` |
| POOL:317 | A | `programs/aspis-pool/src/anchor.rs::PrevalidatedHistoricalAnchorV1::history_page` |
| POOL:318 | B | `programs/aspis-pool/src/anchor.rs::authenticate_historical_anchor_after_prevalidated_state_v1` |
| POOL:319 | D | `programs/aspis-pool/src/anchor.rs::authenticate_historical_anchor_against_state_v1` |
| POOL:320 | B | `programs/aspis-pool/src/anchor.rs::authenticate_historical_anchor_v1` |
| POOL:321 | B | `programs/aspis-pool/src/anchor.rs::bind_envelope_to_state_and_selection` |
| POOL:322 | D | `programs/aspis-pool/src/anchor.rs::load_canonical_pool_state` |
| POOL:323 | B | `programs/aspis-pool/src/anchor.rs::require_history_page_privileges` |
| POOL:324 | A | `programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::CancelPreparedSettlementAccountShapeV1::account_count` |
| POOL:325 | A | `programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::CancelPreparedSettlementAccountShapeV1::has_rollover_shard` |
| POOL:326 | A | `programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::ProgramError::from` |
| POOL:327 | B | `programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::decode_cancel_prepared_settlement_instruction_v1` |
| POOL:328 | B | `programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs::encode_cancel_prepared_settlement_instruction_v1` |
| POOL:329 | D | `programs/aspis-pool/src/deposit.rs::apply_prevalidated_vault_backed_deposit_v1` |
| POOL:330 | D | `programs/aspis-pool/src/deposit.rs::apply_prevalidated_vault_backed_deposit_with_transfer_v1` |
| POOL:331 | A | `programs/aspis-pool/src/deposit.rs::digest_is_canonical` |
| POOL:332 | A | `programs/aspis-pool/src/deposit.rs::finish_deposit_event_v1` |
| POOL:333 | B | `programs/aspis-pool/src/deposit.rs::prepare_deposit_after_state_validation_v1` |
| POOL:334 | B | `programs/aspis-pool/src/deposit.rs::require_disjoint_account_groups` |
| POOL:335 | B | `programs/aspis-pool/src/deposit.rs::validate_request` |
| POOL:336 | A | `programs/aspis-pool/src/deposit_transport.rs::DepositEventReturnDataV1::as_bytes` |
| POOL:337 | B | `programs/aspis-pool/src/deposit_transport.rs::decode_deposit_instruction_v1` |
| POOL:339 | B | `programs/aspis-pool/src/deposit_transport.rs::encode_deposit_event_return_data_v1` |
| POOL:340 | B | `programs/aspis-pool/src/deposit_transport.rs::execute_and_emit_deposit_v1` |
| POOL:341 | C | `programs/aspis-pool/src/deposit_transport.rs::process_prevalidated_vault_backed_deposit_v1` |
| POOL:344 | A | `programs/aspis-pool/src/history.rs::digest_is_canonical` |
| POOL:348 | B | `programs/aspis-pool/src/history.rs::require_program_owned` |
| POOL:351 | D | `programs/aspis-pool/src/history.rs::validate_new_page_account` |
| POOL:356 | B | `programs/aspis-pool/src/instruction.rs::decode_deposit_top_level_v1` |
| POOL:357 | B | `programs/aspis-pool/src/instruction.rs::decode_private_transfer_instruction_v1` |
| POOL:358 | B | `programs/aspis-pool/src/instruction.rs::decode_private_transfer_with_magic_v1` |
| POOL:359 | B | `programs/aspis-pool/src/instruction.rs::decode_statement_common` |
| POOL:360 | B | `programs/aspis-pool/src/instruction.rs::decode_withdrawal_instruction_v1` |
| POOL:361 | B | `programs/aspis-pool/src/instruction.rs::decode_withdrawal_with_magic_v1` |
| POOL:362 | A | `programs/aspis-pool/src/instruction.rs::digest_is_canonical` |
| POOL:363 | B | `programs/aspis-pool/src/instruction.rs::encode_transition_receipt_v1` |
| POOL:364 | B | `programs/aspis-pool/src/instruction.rs::exact_array` |
| POOL:365 | B | `programs/aspis-pool/src/instruction.rs::require_envelope_statement_match` |
| POOL:366 | B | `programs/aspis-pool/src/instruction.rs::require_exact_header` |
| POOL:367 | A | `programs/aspis-pool/src/nullifier.rs::PlannedNullifierMarkerV1::address_bump` |
| POOL:368 | B | `programs/aspis-pool/src/nullifier.rs::PlannedNullifierMarkerV1::encoded_marker` |
| POOL:369 | A | `programs/aspis-pool/src/nullifier.rs::PlannedNullifierMarkerV1::marker` |
| POOL:370 | A | `programs/aspis-pool/src/nullifier.rs::PlannedNullifierMarkerV1::preparation` |
| POOL:376 | B | `programs/aspis-pool/src/nullifier.rs::plan_nullifier_marker_consumption_v1` |
| POOL:378 | B | `programs/aspis-pool/src/nullifier.rs::pool_v1_nullifier_marker_address` |
| POOL:440 | A | `programs/aspis-pool/src/prepared_settlement.rs::AuthenticatedPreparedSettlementActionV1::ordered_commitments` |
| POOL:441 | A | `programs/aspis-pool/src/prepared_settlement.rs::AuthenticatedPreparedSettlementActionV1::withdrawal_amount_and_destination` |
| POOL:442 | A | `programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::anchor_root` |
| POOL:443 | A | `programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::anchor_sequence` |
| POOL:444 | A | `programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::asset_id` |
| POOL:445 | A | `programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::deployment_domain` |
| POOL:446 | A | `programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::nullifier` |
| POOL:447 | A | `programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::ordered_commitments` |
| POOL:448 | A | `programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::pool` |
| POOL:449 | A | `programs/aspis-pool/src/prepared_settlement.rs::CanonicalSettlementStatementV1::transition_kind` |
| POOL:450 | B | `programs/aspis-pool/src/prepared_settlement.rs::append_roots` |
| POOL:451 | C | `programs/aspis-pool/src/prepared_settlement.rs::apply_prepared_settlement_plan_v1` |
| POOL:452 | D | `programs/aspis-pool/src/prepared_settlement.rs::authenticate_prepared_settlement_receipt_claim_v1` |
| POOL:453 | C | `programs/aspis-pool/src/prepared_settlement.rs::authenticate_statement_and_receipt_v1` |
| POOL:454 | A | `programs/aspis-pool/src/prepared_settlement.rs::authenticated_selection_matches_receipt` |
| POOL:455 | B | `programs/aspis-pool/src/prepared_settlement.rs::authorize_prepared_settlement_plan_close_v1` |
| POOL:456 | D | `programs/aspis-pool/src/prepared_settlement.rs::build_prepared_settlement_plan_v1` |
| POOL:457 | B | `programs/aspis-pool/src/prepared_settlement.rs::checked_history_distribution` |
| POOL:458 | B | `programs/aspis-pool/src/prepared_settlement.rs::decode_canonical_statement` |
| POOL:459 | C | `programs/aspis-pool/src/prepared_settlement.rs::history_result_images_match` |
| POOL:460 | B | `programs/aspis-pool/src/prepared_settlement.rs::nullifier_marker_matches` |
| POOL:461 | A | `programs/aspis-pool/src/prepared_settlement.rs::pool_v1_authorization_receipt_account_address` |
| POOL:462 | A | `programs/aspis-pool/src/prepared_settlement.rs::request_commitments` |
| POOL:463 | A | `programs/aspis-pool/src/prepared_settlement.rs::request_transition_kind` |
| POOL:464 | B | `programs/aspis-pool/src/prepared_settlement.rs::source_state_and_result_image_match` |
| POOL:465 | B | `programs/aspis-pool/src/prepared_settlement.rs::validate_receipt_progression` |
| POOL:466 | A | `programs/aspis-pool/src/prepared_settlement.rs::verifier_selection_from_receipt` |
| POOL:467 | B | `programs/aspis-pool/src/prepared_settlement.rs::zeroed_page_box` |
| POOL:468 | A | `programs/aspis-pool/src/prepared_settlement_format.rs::ProgramError::from` |
| POOL:469 | C | `programs/aspis-pool/src/prepared_settlement_format.rs::decode_prepared_settlement_plan_v1` |
| POOL:470 | B | `programs/aspis-pool/src/prepared_settlement_format.rs::decode_receipt` |
| POOL:471 | B | `programs/aspis-pool/src/prepared_settlement_format.rs::decode_rollover_shard_v1` |
| POOL:472 | B | `programs/aspis-pool/src/prepared_settlement_format.rs::digest32` |
| POOL:473 | C | `programs/aspis-pool/src/prepared_settlement_format.rs::encode_prepared_settlement_plan_v1` |
| POOL:474 | B | `programs/aspis-pool/src/prepared_settlement_format.rs::encode_receipt` |
| POOL:475 | B | `programs/aspis-pool/src/prepared_settlement_format.rs::encode_rollover_shard_v1` |
| POOL:476 | B | `programs/aspis-pool/src/prepared_settlement_format.rs::exact_array` |
| POOL:477 | A | `programs/aspis-pool/src/prepared_settlement_format.rs::exact_image_digest_v1` |
| POOL:478 | B | `programs/aspis-pool/src/prepared_settlement_format.rs::exact_ref` |
| POOL:479 | A | `programs/aspis-pool/src/prepared_settlement_format.rs::pool_v1_prepared_settlement_plan_address` |
| POOL:480 | A | `programs/aspis-pool/src/prepared_settlement_format.rs::pool_v1_prepared_settlement_rollover_address` |
| POOL:481 | A | `programs/aspis-pool/src/prepared_settlement_format.rs::receipt_is_exact` |
| POOL:482 | B | `programs/aspis-pool/src/prepared_settlement_format.rs::transition_kind_from_byte` |
| POOL:483 | B | `programs/aspis-pool/src/prepared_settlement_format.rs::zeroed_box` |
| POOL:484 | A | `programs/aspis-pool/src/prepared_settlement_instruction.rs::ProgramError::from` |
| POOL:485 | B | `programs/aspis-pool/src/prepared_settlement_instruction.rs::decode_prepare_settlement_instruction_v1` |
| POOL:486 | B | `programs/aspis-pool/src/prepared_settlement_instruction.rs::exact_array` |
| POOL:487 | B | `programs/aspis-pool/src/prepared_settlement_instruction.rs::transition_kind` |
| POOL:488 | B | `programs/aspis-pool/src/prepared_settlement_instruction.rs::validate_nested_spend` |
| POOL:489 | B | `programs/aspis-pool/src/processor.rs::PoolCpiRuntimeV1::close_program_account` |
| POOL:492 | D | `programs/aspis-pool/src/processor.rs::close_program_account_v1` |
| POOL:493 | D | `programs/aspis-pool/src/processor.rs::create_and_write_marker_v1` |
| POOL:494 | B | `programs/aspis-pool/src/processor.rs::create_next_root_page_if_needed` |
| POOL:495 | D | `programs/aspis-pool/src/processor.rs::create_nullifier_marker_if_needed_v1` |
| POOL:500 | B | `programs/aspis-pool/src/processor.rs::create_prepare_rollover_page_if_needed` |
| POOL:501 | B | `programs/aspis-pool/src/processor.rs::create_program_pda_if_needed` |
| POOL:502 | B | `programs/aspis-pool/src/processor.rs::decode_prepare_settlement_request_v1` |
| POOL:503 | B | `programs/aspis-pool/src/processor.rs::deposit_rolls_to_next_page` |
| POOL:504 | C | `programs/aspis-pool/src/processor.rs::dispatch_selected_verifier_v1` |
| POOL:505 | B | `programs/aspis-pool/src/processor.rs::load_canonical_pool_state` |
| POOL:507 | B | `programs/aspis-pool/src/processor.rs::plan_marker_from_envelope_v1` |
| POOL:508 | C | `programs/aspis-pool/src/processor.rs::plan_prepare_settlement_page_layout_v1` |
| POOL:509 | C | `programs/aspis-pool/src/processor.rs::plan_settle_prepared_layout_v1` |
| POOL:510 | C | `programs/aspis-pool/src/processor.rs::plan_spend_page_layout_v1` |
| POOL:511 | D | `programs/aspis-pool/src/processor.rs::process_cancel_prepared_settlement_with_runtime_v1` |
| POOL:512 | D | `programs/aspis-pool/src/processor.rs::process_deposit_with_runtime_v1` |
| POOL:514 | D | `programs/aspis-pool/src/processor.rs::process_prepare_settlement_with_runtime_v1` |
| POOL:515 | C | `programs/aspis-pool/src/processor.rs::process_private_transfer_with_runtime_v1` |
| POOL:516 | D | `programs/aspis-pool/src/processor.rs::process_settle_prepared_with_runtime_v1` |
| POOL:517 | D | `programs/aspis-pool/src/processor.rs::process_withdrawal_with_runtime_v1` |
| POOL:518 | D | `programs/aspis-pool/src/processor.rs::require_fresh_rent_exempt_program_pda` |
| POOL:520 | D | `programs/aspis-pool/src/processor.rs::require_prepared_plan_account_v1` |
| POOL:521 | B | `programs/aspis-pool/src/processor.rs::require_spend_capacity` |
| POOL:526 | D | `programs/aspis-pool/src/processor.rs::state_accounts_for_append_v1` |
| POOL:528 | B | `programs/aspis-pool/src/processor.rs::validate_spend_binding_v1` |
| POOL:529 | A | `programs/aspis-pool/src/registry.rs::AuthenticatedVerifierSelectionV1::authenticated_at_slot` |
| POOL:531 | A | `programs/aspis-pool/src/registry.rs::AuthenticatedVerifierSelectionV1::matches_policy` |
| POOL:533 | A | `programs/aspis-pool/src/registry.rs::AuthenticatedVerifierSelectionV1::registry_generation` |
| POOL:542 | A | `programs/aspis-pool/src/settle_prepared_instruction.rs::ProgramError::from` |
| POOL:543 | B | `programs/aspis-pool/src/settle_prepared_instruction.rs::decode_settle_prepared_instruction_v1` |
| POOL:544 | B | `programs/aspis-pool/src/settle_prepared_instruction.rs::transition_kind` |
| POOL:545 | B | `programs/aspis-pool/src/settle_prepared_instruction.rs::validate_statement` |
| POOL:546 | A | `programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::as_state` |
| POOL:547 | D | `programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::decode_account` |
| POOL:548 | D | `programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::decode_account_from_program_invariant` |
| POOL:549 | A | `programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::deref` |
| POOL:550 | A | `programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::reconstructed_tree` |
| POOL:551 | B | `programs/aspis-pool/src/state.rs::CanonicalPoolStateV1::require_same_writable_account` |
| POOL:552 | A | `programs/aspis-pool/src/state.rs::PoolStateV1::current_root_sequence` |
| POOL:553 | B | `programs/aspis-pool/src/state.rs::PoolStateV1::decode` |
| POOL:554 | B | `programs/aspis-pool/src/state.rs::PoolStateV1::decode_boxed` |
| POOL:555 | B | `programs/aspis-pool/src/state.rs::PoolStateV1::decode_boxed_from_program_invariant` |
| POOL:556 | B | `programs/aspis-pool/src/state.rs::PoolStateV1::decode_boxed_with_validated_tree` |
| POOL:557 | C | `programs/aspis-pool/src/state.rs::PoolStateV1::decode_from_program_invariant` |
| POOL:558 | B | `programs/aspis-pool/src/state.rs::PoolStateV1::decode_with_validated_tree` |
| POOL:559 | B | `programs/aspis-pool/src/state.rs::PoolStateV1::validate_encoding` |
| POOL:560 | B | `programs/aspis-pool/src/state.rs::PoolStateV1::write_encoding_prevalidated` |
| POOL:561 | B | `programs/aspis-pool/src/state.rs::exact_state_array` |
| POOL:562 | A | `programs/aspis-pool/src/state.rs::pool_v1_state_address` |
| POOL:563 | A | `programs/aspis-pool/src/transition.rs::AuthorizedAppendV1::count` |
| POOL:564 | B | `programs/aspis-pool/src/transition.rs::AuthorizedAppendV1::validate_leaves` |
| POOL:565 | A | `programs/aspis-pool/src/transition.rs::AuthorizedSourceStateV1<'a>::as_state` |
| POOL:566 | B | `programs/aspis-pool/src/transition.rs::AuthorizedSourceStateV1<'a>::prepare` |
| POOL:567 | B | `programs/aspis-pool/src/transition.rs::PreparedAuthorizedAppendV1::validate_inherited_state_and_cursor` |
| POOL:568 | B | `programs/aspis-pool/src/transition.rs::PrevalidatedCurrentHistoryV1::require_matches` |
| POOL:569 | B | `programs/aspis-pool/src/transition.rs::PrevalidatedNewHistoryPageV1::require_matches` |
| POOL:570 | B | `programs/aspis-pool/src/transition.rs::append_one_from_program_invariant` |
| POOL:571 | D | `programs/aspis-pool/src/transition.rs::apply_authorized_append_after_checked_state_v1` |
| POOL:572 | C | `programs/aspis-pool/src/transition.rs::apply_authorized_append_after_prevalidated_history_v1` |
| POOL:573 | C | `programs/aspis-pool/src/transition.rs::apply_authorized_append_after_prevalidated_v1` |
| POOL:574 | D | `programs/aspis-pool/src/transition.rs::apply_authorized_append_after_v1` |
| POOL:575 | A | `programs/aspis-pool/src/transition.rs::map_tree_error` |
| POOL:576 | C | `programs/aspis-pool/src/transition.rs::prepare_append_from_canonical_state` |
| POOL:577 | B | `programs/aspis-pool/src/transition.rs::prepare_authorized_append_images_v1` |
| POOL:578 | B | `programs/aspis-pool/src/transition.rs::prepare_checked_append` |
| POOL:579 | B | `programs/aspis-pool/src/transition.rs::prevalidate_new_history_page_v1` |
| POOL:580 | D | `programs/aspis-pool/src/transition.rs::validate_current_history` |
| POOL:581 | D | `programs/aspis-pool/src/transition.rs::validate_current_history_after_prevalidated_anchor_v1` |
| POOL:591 | B | `programs/aspis-pool/src/vault.rs::plan_legacy_deposit_transfer_v1` |
| POOL:593 | B | `programs/aspis-pool/src/vault.rs::plan_legacy_withdrawal_transfer_v1` |
| POOL:601 | A | `programs/aspis-pool/src/verifier_dispatch.rs::SolanaVerifierDispatchRuntimeV1::clear_return_data` |
| POOL:602 | A | `programs/aspis-pool/src/verifier_dispatch.rs::SolanaVerifierDispatchRuntimeV1::get_return_data` |
| POOL:604 | D | `programs/aspis-pool/src/verifier_dispatch.rs::authenticate_proof_account_body_v1` |
| POOL:605 | B | `programs/aspis-pool/src/verifier_dispatch.rs::authenticate_verifier_return_data_v1` |
| POOL:606 | D | `programs/aspis-pool/src/verifier_dispatch.rs::derive_verifier_dispatch_claim_v1` |
| POOL:607 | C | `programs/aspis-pool/src/verifier_dispatch.rs::dispatch_authenticated_verifier_readonly_v1` |
| POOL:608 | C | `programs/aspis-pool/src/verifier_dispatch.rs::dispatch_authenticated_verifier_readonly_with_runtime_v1` |
| POOL:609 | D | `programs/aspis-pool/src/verifier_dispatch.rs::invoke_freshly_planned_verifier_v1` |
| POOL:610 | C | `programs/aspis-pool/src/verifier_dispatch.rs::plan_authenticated_verifier_dispatch_v1` |
| POOL:611 | B | `programs/aspis-pool/src/verifier_dispatch.rs::require_exact_readonly_cpi_accounts_v1` |
| POOL:612 | B | `programs/aspis-pool/src/verifier_dispatch.rs::require_selected_verifier_program_account` |
| POOL:613 | A | `programs/aspis-pool/src/verifier_dispatch.rs::supported_verifier_loader` |
