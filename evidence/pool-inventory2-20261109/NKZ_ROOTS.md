# New release Pool instruction roots

Target not yet established. Pool source b936275465600469312d1f058cdc91ea2a11f3dc; crates 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. SDK entrypoint! is processor.rs:62; process_instruction starts:491. Exact SBF command and feature list are retained in NKZ_aspis_pool.command.json/NKZ_DEPLOYED_BUILD.json. Features: default, pair-forest-account-evidence, pair-forest-source-invariant-audit, pair-forest-source-result-invariant-audit, pair-forest-verifier-lane-invariant-audit, r1-split-checkpoint.

ON is the conservative spend/lifecycle union, not a claim that all roots execute in one two-transaction trace. AS8C is retained conservatively for checkpoint preparation. Four dispatcher alternatives are active; three optional source alternatives are cfg-disabled. Every OFF alternative is shown for owner review.

| Magic | ON/OFF | Source root and line | Reason |
|---|---|---|---|
| AS8I | OFF | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1:1994` | Creates master/lane state; initialization before a spend. |
| AS8C | ON | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1:2130` | Retains the authenticated forest checkpoint consumed by terminal settlement. |
| AS8D | ON | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1:988` | Vault-backed deposit updates the forest used by the spend. |
| ASQ8 | ON | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_v1:1823` | Deployed compact verifier-gated terminal, transfer/withdrawal continuation. |
| ASF8 | OFF | `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_full_asf8_v1:1890` | Full transport is cfg-disabled in pinned deployed features. |
| ASJP | OFF | `programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1:277` | pair-afterstate-evidence is cfg-disabled in deployed features. |
| ASJW | OFF | `programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1:418` | pair-afterstate-evidence is cfg-disabled in deployed features; held-site review retained separately. |

Removed alternatives (no dispatch arm; source fallback returns InvalidInstructionData):

| Magic | Former class | Former root | New disposition |
|---|---|---|---|
| ASIN | OFF | `programs/aspis-pool/src/processor.rs::process_initialize_with_runtime_v1` | REMOVED; rejects |
| ASDI | ON | `programs/aspis-pool/src/processor.rs::process_deposit_with_runtime_v1` | REMOVED; rejects |
| ASPP | ON | `programs/aspis-pool/src/processor.rs::process_prepare_settlement_with_runtime_v1` | REMOVED; rejects |
| ASPX | ON | `programs/aspis-pool/src/processor.rs::process_cancel_prepared_settlement_with_runtime_v1` | REMOVED; rejects |
| ASPF | ON | `programs/aspis-pool/src/processor.rs::process_settle_prepared_with_runtime_v1` | REMOVED; rejects |
| ASPT | ON | `programs/aspis-pool/src/processor.rs::process_private_transfer_with_runtime_v1` | REMOVED; rejects |
| ASWD | ON | `programs/aspis-pool/src/processor.rs::process_withdrawal_with_runtime_v1` | REMOVED; rejects |

No standalone admin, registry-maintenance or close instruction remains. Short/unknown inputs reject; return data is cleared initially and on errors. The native/SBF difference is explicit: the transaction-level stack-height check is Solana-only, while native cfg excludes that syscall gate; the source magic/feature dispatch is otherwise the same. Tests are cfg(test), not deployed roots. Generic ASJP/ASJW bodies present in MIR do not establish production reachability; OFF edges and owners remain visible. SDK macro/allocator/panic/derives/std/external calls are boundary records, under NGB source-occurrence semantics.
