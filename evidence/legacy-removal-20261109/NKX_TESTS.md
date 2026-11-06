# Pool test receipts

All tests use optimized `cargo test --release --locked --offline -j 4`, one
admitted 6G/8G/Swap0/Tasks64 scope at a time, 600-second timeout, CPU affinity
0–3 after the initial thread-spawn failure. No timeout/OOM or unchanged failed
shape retry occurred. The frozen Cargo.lock hash is checked before/after.

| Source/configuration | Passed | Failed | Evidence |
|---|---:|---:|---|
| Frozen 4bb3b3f, deployed features | 118 unit + 2 integration | 0 | NKX_baseline2 |
| Removed source, deployed features | 67 unit | 0 | NKX_tests-deployed2 |
| Removed source, default features | 36 unit | 0 | NKX_tests-default |
| Removed source, deployed plus disabled ASJP/ASJW/ASF8 routes | 67 unit | 0 | NKX_tests-disabled |
| All remaining tests, including five audit-only tests | 72 unit | 0 | NKX_tests-all |

The frozen source contains 125 `#[test]` functions (five need extra audit
features); the final source contains 72. Removed: 54. Added: one legacy-magic
rejection test. Native deployed count: 120 → 67 = 120 − 54 + 1. The old external
payment_relation_abi tests exercise removed public decoders and are removed;
pair-forest native account/state/CPI integration tests in pair_forest.rs and
pair_processor.rs remain unchanged and run in the feature-enabled suites.

The new rejection test checks each of ASIN/ASDI/ASPT/ASWD/ASPP/ASPF/ASPX at
four input lengths, returning the existing InvalidInstructionData error.
Source validation independently verifies that none has a dispatch arm.

Initial failures retained:
- baseline: compiler/linker thread spawning exhausted TasksMax=64. The revised
  own runner restricts affinity to four CPUs; no cap was raised.
- tests-deployed: unresolved shared AS8I initialization codecs. Restore their
  exact frozen text, retain the shared constants and add source dependencies
  to the independent byte gate; tests-deployed2 then passes.
- Static validator initially associated the first overloaded conversion with
  an inventory key that denoted the last; use stable duplicate entries and
  match the inventory's final owner. Both direct old/new comparisons and
  inventory hashes now agree. No build scope consumed by this validator fix.

Each receipt records exact command, source manifest, revision label, wall,
peak RSS, swap and exit. Post-removal test receipts labelled bf38bb69dbe use
that revision plus the restored-codec source snapshot (the exact final source
manifest), not the uncorrected committed tree. ELF receipts use the later
validated source commit. #print axioms: N/A; 0 Lean/Kani/extraction.

## Every removed test (frozen file:line)

- `programs/aspis-pool/src/anchor.rs:378` `tests::retained_sequence_one_authenticates_after_sequence_two_is_appended`
- `programs/aspis-pool/src/anchor.rs:394` `tests::exact_current_root_also_authenticates_without_mutation`
- `programs/aspis-pool/src/anchor.rs:405` `tests::prevalidated_state_adapter_is_exact_and_still_rejects_page_corruption`
- `programs/aspis-pool/src/anchor.rs:516` `tests::wrong_root_domain_selection_future_or_page_fails_closed`
- `programs/aspis-pool/src/anchor.rs:573` `tests::history_page_signer_is_rejected_without_writes`
- `programs/aspis-pool/src/anchor.rs:588` `tests::older_page_writable_privilege_is_rejected`
- `programs/aspis-pool/src/cancel_prepared_settlement_instruction.rs:93` `tests::cancel_prepared_wire_is_exact_shape_bound_and_canonical`
- `programs/aspis-pool/src/deposit.rs:369` `tests::backed_deposit_transfers_exact_u32_then_appends_one_note_and_root`
- `programs/aspis-pool/src/deposit.rs:567` `tests::prevalidated_deposit_is_byte_exact_to_standalone_kernel`
- `programs/aspis-pool/src/deposit.rs:821` `tests::failed_transfer_leaves_pool_and_history_byte_exact`
- `programs/aspis-pool/src/deposit.rs:965` `tests::invalid_amount_payload_and_token2022_shape_fail_before_transfer`
- `programs/aspis-pool/src/deposit_transport.rs:332` `tests::canonical_instruction_round_trip_rejects_wrong_version_reserved_and_trailing`
- `programs/aspis-pool/src/deposit_transport.rs:363` `tests::successful_kernel_result_sets_exact_receipt_payload_once`
- `programs/aspis-pool/src/deposit_transport.rs:383` `tests::failed_kernel_result_never_sets_return_data`
- `programs/aspis-pool/src/instruction.rs:711` `tests::initialization_is_exact_and_rejects_trailing_reserved_and_policy_confusion`
- `programs/aspis-pool/src/instruction.rs:746` `tests::private_transfer_round_trip_binds_both_outputs_and_all_common_fields`
- `programs/aspis-pool/src/instruction.rs:784` `tests::withdrawal_round_trip_rejects_zero_amount_wrong_kind_and_trailing_data`
- `programs/aspis-pool/src/prepared_settlement.rs:2122` `tests::public_preparation_processor_persists_exact_core_and_rejects_privilege_aliases`
- `programs/aspis-pool/src/prepared_settlement.rs:2297` `tests::public_preparation_processor_persists_exact_rollover_core_and_shard`
- `programs/aspis-pool/src/prepared_settlement.rs:2492` `tests::public_cancel_core_only_authenticates_layout_authority_and_digest_before_refund`
- `programs/aspis-pool/src/prepared_settlement.rs:2646` `tests::public_cancel_rollover_authenticates_shard_and_orders_late_failure_before_success`
- `programs/aspis-pool/src/prepared_settlement.rs:2841` `tests::public_final_private_transfer_copies_rollover_images_closes_plans_and_rejects_replay`
- `programs/aspis-pool/src/prepared_settlement.rs:3071` `tests::public_final_withdrawal_uses_authenticated_custody_delta_and_success_only_receipt`
- `programs/aspis-pool/src/prepared_settlement.rs:3277` `tests::withdrawal_and_private_transfer_are_byte_exact_with_the_direct_path`
- `programs/aspis-pool/src/prepared_settlement.rs:3283` `tests::rollover_encoder_owned_output_images_fit_default_solana_heap`
- `programs/aspis-pool/src/prepared_settlement.rs:3297` `tests::two_leaf_plan_preserves_both_chronological_roots_across_page_boundary`
- `programs/aspis-pool/src/prepared_settlement.rs:3306` `tests::every_plan_byte_is_authenticated`
- `programs/aspis-pool/src/prepared_settlement.rs:3349` `tests::rollover_shard_is_mutually_bound_and_semantically_checked`
- `programs/aspis-pool/src/prepared_settlement.rs:3439` `tests::stale_pool_pages_receipt_and_time_fail_closed`
- `programs/aspis-pool/src/prepared_settlement.rs:3539` `tests::asra_pending_wrapper_binding_pda_and_nested_receipt_fail_closed`
- `programs/aspis-pool/src/prepared_settlement.rs:3608` `tests::preparation_rejects_self_consistent_receipt_for_non_pool_historical_root`
- `programs/aspis-pool/src/prepared_settlement.rs:3752` `tests::registry_selection_is_active_exact_and_reauthenticated_at_settlement`
- `programs/aspis-pool/src/prepared_settlement.rs:3956` `tests::reauthenticated_root_receipt_and_output_order_substitutions_reject`
- `programs/aspis-pool/src/prepared_settlement.rs:4020` `tests::authority_sequence_parallel_plan_and_close_bindings_are_exact`
- `programs/aspis-pool/src/prepared_settlement.rs:4106` `tests::substituted_statement_and_nullifier_marker_reject`
- `programs/aspis-pool/src/prepared_settlement_instruction.rs:160` `tests::prepared_settlement_instruction_is_exact_and_nested_kind_bound`
- `programs/aspis-pool/src/processor.rs:2811` `tests::precreated_initialization_reaches_dispatch_without_cpi_and_emits_only_after_success`
- `programs/aspis-pool/src/processor.rs:2927` `tests::private_transfer_failure_alias_rejection_then_success_is_exactly_one_to_two`
- `programs/aspis-pool/src/processor.rs:3338` `tests::accepted_withdrawal_updates_exact_balances_marker_tree_and_success_receipt`
- `programs/aspis-pool/src/settle_prepared_instruction.rs:127` `tests::settle_prepared_wire_is_exact_and_nested_kind_bound`
- `programs/aspis-pool/src/state.rs:516` `tests::exact_state_image_roundtrips_and_rejects_type_reserved_cursor_and_pool_confusion`
- `programs/aspis-pool/src/state.rs:577` `tests::specialized_genesis_is_exactly_the_generic_checked_tree_and_fails_closed`
- `programs/aspis-pool/src/state.rs:606` `tests::program_invariant_decoder_has_one_explicit_relation_boundary`
- `programs/aspis-pool/src/transition.rs:898` `tests::program_invariant_append_is_byte_exact_across_carry_boundaries`
- `programs/aspis-pool/src/transition.rs:956` `tests::genesis_accepts_canonical_pool_pda_without_signer`
- `programs/aspis-pool/src/transition.rs:984` `tests::genesis_rejects_noncanonical_pool_address_without_writes`
- `programs/aspis-pool/src/transition.rs:1017` `tests::genesis_rejects_wrong_page_address_and_nonzero_account_without_writes`
- `programs/aspis-pool/src/transition.rs:1076` `tests::one_and_two_leaf_transitions_persist_matching_roots`
- `programs/aspis-pool/src/transition.rs:1155` `tests::prevalidated_append_is_byte_exact_and_rejects_pool_substitution_before_callback`
- `programs/aspis-pool/src/transition.rs:1374` `tests::page_rollover_is_exact_and_failure_before_next_page_is_atomic`
- `programs/aspis-pool/src/transition.rs:1457` `tests::two_leaf_append_splits_exactly_across_page_boundary`
- `programs/aspis-pool/src/transition.rs:1551` `tests::final_append_reaches_full_tree_and_future_append_fails_closed`
- `programs/aspis-pool/tests/payment_relation_abi.rs:39` `private_transfer_relation_encoding_is_byte_exact_to_pool_payload`
- `programs/aspis-pool/tests/payment_relation_abi.rs:83` `withdrawal_relation_encoding_is_byte_exact_to_pool_payload`
