# Pool instruction roots

Target not yet established. Frozen entry: `processor.rs:2412`, SDK `entrypoint!` at `processor.rs:130`; dispatch `2429–2609`. The exact pinned ELF enables `r1-split-checkpoint`, `pair-forest-source-invariant-audit`, `pair-forest-source-result-invariant-audit` and their recorded dependencies. Cargo default-off comments are not the deployed feature authority. See NKS_DEPLOYED_BUILD.json.

ON means the conservative spend/lifecycle union requested for owner review; it does not assert all nine roots run in one two-transaction spend. AS8C is included as checkpoint preparation, and legacy spend alternatives stay included.

| Magic | ON/OFF | Frozen source root | Reason |
|---|---|---|---|
| AS8I | OFF | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1:1994` | Creates master/lane state; initialization before a spend. |
| AS8C | ON | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1:2130` | Retains the authenticated forest checkpoint consumed by terminal settlement. |
| AS8D | ON | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1:988` | Vault-backed deposit updates the forest used by the spend. |
| ASQ8 | ON | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_v1:1823` | Deployed compact verifier-gated terminal, transfer/withdrawal continuation. |
| ASF8 | OFF | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_full_asf8_v1:1890` | Full transport is cfg-disabled in pinned deployed features. |
| ASIN | OFF | `programs/aspis-pool/src/processor.rs::process_initialize_with_runtime_v1:625` | Initializes legacy Pool accounts before a spend. |
| ASDI | ON | `programs/aspis-pool/src/processor.rs::process_deposit_with_runtime_v1:738` | Legacy vault-backed deposit; conservatively retained deployed alternative. |
| ASPP | ON | `programs/aspis-pool/src/processor.rs::process_prepare_settlement_with_runtime_v1:1167` | Creates the retained prepared-settlement state. |
| ASPX | ON | `programs/aspis-pool/src/processor.rs::process_cancel_prepared_settlement_with_runtime_v1:1484` | Cancels/refunds a prepared settlement and closes its accounts. |
| ASPF | ON | `programs/aspis-pool/src/processor.rs::process_settle_prepared_with_runtime_v1:1674` | Consumes the prepared plan and persists settlement. |
| ASJP | OFF | `programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1:277` | pair-afterstate-evidence is cfg-disabled in deployed features. |
| ASJW | OFF | `programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1:418` | pair-afterstate-evidence is cfg-disabled in deployed features; held-site review retained separately. |
| ASPT | ON | `programs/aspis-pool/src/processor.rs::process_private_transfer_with_runtime_v1:2024` | Verifier-gated legacy private transfer; retained alternative. |
| ASWD | ON | `programs/aspis-pool/src/processor.rs::process_withdrawal_with_runtime_v1:2189` | Verifier-gated legacy withdrawal; retained alternative. |

No registry-maintenance/admin/standalone-close dispatch branch in Pool; close_program_account_v1 is an ON cancel/settle callee, not an OFF instruction. Invalid/short input rejects; entry clears return data before dispatch and again on error. OFF routes are not silently dropped: NKS_GRAPH.json keeps their dispatch edges and NKS_INVENTORY.json numbers the four OFF exclusive-guard owners separately. ASJP/ASJW generic bodies exist in MIR although their dispatcher branches are cfg-disabled; body emission is not deployed reachability.

The SDK macro entry, allocator, panic, generated constructors/derives, std and external SDK functions are explicitly classified boundary/codegen records, not new project-source rows (NGB/NDT semantics). No account close or refund is executed by this inventory.
