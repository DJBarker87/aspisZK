# NKH physical association distances

Target not yet established. Recomputed from599 retained function occurrences after the full combined gate admitted28candidate occurrences. These are conditional native/source associations; entry/caller/runtime/source-to-ELF/headline obligations remain.

| Part | Total | CLOSED | OPEN | QUALIFIED |
|---|---:|---:|---:|---:|
| (ao)(3)(b) | 53 | 38 | 15 | 0 |
| (ao)(3)(c) | 546 | 504 | 42 | 0 |

Entry(b)38/53 and native forest(c)504/546 CLOSED;15entry and42forest occurrences remain OPEN,57total. No parent or production association is inferred from a helper closure.

## Shortest OPEN spine paths

BFS over the retained canonical call graph. The spurious-by-name069→202 edge remains visible under(az)(1).

TX1: TX1:330 process_r1_cost_probe_instruction [OPEN] → TX1:333 process [OPEN] → TX1:344 stage1 [OPEN] → TX1:345 stage1_owned [OPEN] → TX1:328 first_decoded [OPEN] → TX1:094 tx1 [OPEN].

OPEN distance 6; 5 call edges.

TX2: TX2:213 process_r1_cost_probe_instruction [OPEN] → TX2:221 process [OPEN] → TX2:240 stage2 [OPEN] → TX2:241 stage2_owned [OPEN] → TX2:064 tx2_authenticated [OPEN] → TX2:065 tx2_common [OPEN] → TX2:115 finish_relation [CLOSED].

OPEN distance 6; 6 call edges.

(aw) NJW-aw-TX2:115-off-domain CLOSED by the full combined gate: NJU_GeneralFinishRoot.finish/ported establishes a SAME-native-G arbitrary-current-word full Result/prefix law with final length2048 and no NoBad/history/persistence/success premise, and this job completed its all-root gate. It remains outside599. Original115 stays CLOSED as stated;065 remains OPEN.

## OPEN rows grouped by source and live owner

### crates/aspis-core/src/circle.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:NGB004 | secure_ood_circle_point_from_parameter | UNOWNED in current brief; S2 lead routing |
| TX1:NGB006 | secure_circle_point_from_parameter | UNOWNED in current brief; S2 lead routing |

### crates/aspis-core/src/field.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:036 | qm31_accumulate_product_channels | UNOWNED in current brief; S2 lead routing |
| TX1:040 | qm31_sum_products2 | UNOWNED in current brief; S2 lead routing |
| TX1:041 | qm31_sum_products3 | UNOWNED in current brief; S2 lead routing |
| TX1:043 | qm31_sum_products4 | UNOWNED in current brief; S2 lead routing |
| TX1:044 | qm31_sum_products_small | UNOWNED in current brief; S2 lead routing |

### crates/aspis-core/src/r0_transcript.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:069 | queries_from_pairs | NKA_ claims2 |

### crates/aspis-core/src/transcript.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:NGB002 | circle_fallback_point | UNOWNED in current brief; S2 lead routing |

### crates/aspis-r1-cost-probe/src/candidate.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:081 | batch_merkle | NKB_ batch-merkle2 |
| TX1:082 | batch_merkle_values | NKB_ batch-merkle2 |
| TX1:083 | batch_tree | NKB_ batch-merkle2 |
| TX1:084 | canonical_scan | NKB_ batch-merkle2 |
| TX1:087 | prepare | UNOWNED in current brief; S2 lead routing |
| TX1:094 | tx1 | UNOWNED in current brief; S2 lead routing |
| TX2:053 | batch_merkle | NKB_ batch-merkle2 |
| TX2:054 | batch_merkle_values | NKB_ batch-merkle2 |
| TX2:055 | batch_tree | NKB_ batch-merkle2 |
| TX2:064 | tx2_authenticated | UNOWNED in current brief; S2 lead routing |
| TX2:065 | tx2_common | NKE_ tx2-native9 (M01 join) |

### crates/aspis-r1-cost-probe/src/r1_semantic.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:129 | claims | NKA_ claims2 |
| TX1:136 | verify_finish | NKA_ claims2 |
| TX1:137 | verify_observed | UNOWNED in current brief; S2 lead routing |

### crates/aspis-r1-cost-probe/src/verifier.rs

| Row | Function | Owning live job |
|---|---|---|
| TX2:124 | resume | UNOWNED in current brief; S2 lead routing |

### crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:218 | evaluate_with_selectors | UNOWNED in current brief; S2 lead routing |
| TX1:220 | finish_selector_tensor_basis | UNOWNED in current brief; S2 lead routing |
| TX1:225 | qm31_sum_products_up_to4 | UNOWNED in current brief; S2 lead routing |

### crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:232 | add_schedule_lanes | UNOWNED in current brief; S2 lead routing |
| TX1:233 | add_value_lanes | UNOWNED in current brief; S2 lead routing |
| TX1:234 | append_level_packed_selector_tensor | UNOWNED in current brief; S2 lead routing |
| TX1:235 | append_levels_packed_selector_tensor | UNOWNED in current brief; S2 lead routing |
| TX1:237 | composition_parts | UNOWNED in current brief; S2 lead routing |
| TX1:250 | public_digest_packed | UNOWNED in current brief; S2 lead routing |
| TX1:251 | public_digest_packed_selector_tensor | UNOWNED in current brief; S2 lead routing |
| TX1:256 | r0::Public<'a>::terminal_qm31 | UNOWNED in current brief; S2 lead routing |
| TX1:260 | semantic_initial_and_absorption | UNOWNED in current brief; S2 lead routing |
| TX1:261 | semantic_packed | UNOWNED in current brief; S2 lead routing |
| TX1:263 | terminal_parts | UNOWNED in current brief; S2 lead routing |

### crates/aspis-statement/src/state_only_poseidon.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:308 | evaluate_state_only_poseidon_oracle_projected | NKG_ poseidon-state |
| TX1:321 | interpolate_three_constant_columns | NKG_ poseidon-state |
| TX1:323 | interpolated_full_pair_packed | NKG_ poseidon-state |
| TX1:324 | interpolated_internal_pair | NKG_ poseidon-state |

### programs/r1-cost-probe/src/lib.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:328 | first_decoded | UNOWNED in current brief; S2 lead routing |
| TX1:330 | process_r1_cost_probe_instruction | UNOWNED in current brief; S2 lead routing |
| TX2:213 | process_r1_cost_probe_instruction | UNOWNED in current brief; S2 lead routing |

### programs/r1-cost-probe/src/r1_pool_adapter.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:333 | process | UNOWNED in current brief; S2 lead routing |
| TX2:216 | decode_checkpoint_box | NKF_ tx2-adapters |
| TX2:217 | decode_lane_from_pool_release | NKF_ tx2-adapters |
| TX2:218 | decode_master_box | NKF_ tx2-adapters |
| TX2:221 | process | UNOWNED in current brief; S2 lead routing |

### programs/r1-cost-probe/src/r1_pool_adapter_owned.rs

| Row | Function | Owning live job |
|---|---|---|
| TX1:344 | stage1 | UNOWNED in current brief; S2 lead routing |
| TX1:345 | stage1_owned | UNOWNED in current brief; S2 lead routing |
| TX2:233 | authenticate_asq8_accounts | NKF_ tx2-adapters |
| TX2:234 | authenticate_invariant_release_registry | NKF_ tx2-adapters |
| TX2:240 | stage2 | UNOWNED in current brief; S2 lead routing |
| TX2:241 | stage2_owned | UNOWNED in current brief; S2 lead routing |
| TX2:242 | validate_asq8 | NKF_ tx2-adapters |

## Explicit unowned OPEN occurrences

TX1:036, TX1:040, TX1:041, TX1:043, TX1:044, TX1:087, TX1:094, TX1:137, TX1:218, TX1:220, TX1:225, TX1:232, TX1:233, TX1:234, TX1:235, TX1:237, TX1:250, TX1:251, TX1:256, TX1:260, TX1:261, TX1:263, TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:064, TX2:124, TX2:213, TX2:221, TX2:240, TX2:241, TX1:NGB002, TX1:NGB004, TX1:NGB006.

## (ao)(3)(d): named Pool obligations

The599 verifier rows contain ZERO production Pool-consumer occurrences. Three inherited helper rows remain CLOSED: pair_forest_dispatch.supported_loader, processor.require_transaction_level_invocation_v1 and error.convertPoolError. This is not3/3 production Pool closure. No finite complete deployed-root Pool inventory is available in this basis; the following named obligations remain separate.

| Obligation | Status | Exact missing association |
|---|---|---|
| NIB-P1 | OPEN | SAME CPI invocation, emitted bytes/program-id/register continuity, immediate read, no intervening CPI/set/clear. RuntimeReturnData/ReturnDataClear do not prove the caller. |
| NIB-P2 | OPEN | Actual production validation dictionary, full Result/error and SAME decoded statement/result. |
| NIB-P3 | OPEN | Actual production lane dictionary and SAME source state/carriers. |
| NIB-P4 | OPEN | Complete settlement/withdrawal/mutation/borrow/cleanup frame through actual production continuation. |
| POOL.prefix_to_cpi | OPEN | Production B prefix, reached accounts, exact CPI/meta/payload and live-guard domains. |
| POOL.read_to_settlement | PROVED-conditional model / production OPEN | NIB_ReadToSettlement.read_to_settlement is retained, with P1..P4 producers uninstantiated. |

### Four held CPI/callback sites

All four remain OPEN; NIO and NIZ supply local support, zero complete actual-site certificates. RuntimeEntrypointAdmission-Pool now supplies the SAME initial seven fields, while reached layouts, uniqueness, physical-cell use, CPI frames and source/native argument association remain to prove. No RuntimeCpiReadonlyEntry7 use.

| Actual source owner | Guarded data | Passed indices / remaining scope | Status |
|---|---|---|---|
| pair_forest.rs::process_pair_forest_deposit_with_runtime_v1 | accounts[1], accounts[2] if fresh/same, accounts[3] if rollover | token_start+[1,0,3,2,4], token_start=3 or4; reached case split, actual metas/payload/token-program and SAME-cell separation | OPEN |
| pair_forest.rs::process_pair_forest_terminal_with_verifier_v1 | accounts[2], accounts[3] if genesis/same, accounts[4] if rollover, accounts[cursor] marker | token_start+[1,0,2,3,4], cursor=4 or5, token_start=cursor+7; full reached native/CPI frame | OPEN |
| pair_processor.rs::process_pair_withdrawal_with_verifier_v1 | history selected current/next index<marker_index, accounts[0], accounts[marker_index] | proof_index+1+[1,0,2,3,4], proof_index=marker_index+4; exact native/meta/CPI association | OPEN |
| transition.rs::apply_authorized_append_after_checked_state_v1 | pool, optional current/next pages | All deployed before_persist deposit/withdrawal/no-op instantiations; marker creation, token CPI, validation and write footprints | OPEN |

Source-level direct-site index separation is NIO/NIZ inspection, not a native certificate; callback separation is not universal. A reached overlap must be reported as a liveness finding, never assumed away.

### Thirteen exclusive-guard owners

Full original-source ScopeRun/native/counter/child/cleanup association remains OPEN for every owner. Reference-only counter scopes and fixed-prefix helper windows are supporting facts. No owner is completed by the combined import.

| Exact exclusive-guard owner | Status |
|---|---|
| programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1 | OPEN |
| programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1 | OPEN |
| programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1 | OPEN |
| programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1 | OPEN |
| programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1 | OPEN |
| programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1 | OPEN |
| programs/aspis-pool/src/processor.rs::close_program_account_v1 | OPEN |
| programs/aspis-pool/src/processor.rs::process_prepare_settlement_with_runtime_v1 | OPEN |
| programs/aspis-pool/src/processor.rs::process_settle_prepared_with_runtime_v1 | OPEN |
| programs/aspis-pool/src/processor.rs::create_and_write_marker_v1 | OPEN |
| programs/aspis-pool/src/processor.rs::process_withdrawal_with_runtime_v1 | OPEN |
| programs/aspis-pool/src/transition.rs::initialize_pool_accounts_v1 | OPEN |
| programs/aspis-pool/src/transition.rs::apply_authorized_append_after_checked_state_v1 | OPEN |

RuntimeEntrypointAdmission-Pool: ADDED-LEAD-20261107 under(ap), existing inventory design/TRUST-INVENTORY-APPENDIX-DRAFT-20261027.md:45. Fields verbatim: valid, freshGuards, noExternalBorrows, liveAccount, counterZero, sharedCellsOnlyEqualKeys, duplicateKeysShareCell. Initial Pool entrypoint relation only; no CPI frame, token-program behavior or success. NJK documents the lead addition and changes no trust inventory/ledger trust row.

RuntimePersistence remains accepted data-only trust. (ao)(3)(a) extraction stays accepted P6/D188/pinning, and(e) queries stays the L154 statement parameter. Owner decision(aj)(a) remains PENDING. Exact next(d) inventory deliverable: an authoritative deployed-root Pool closure with numbered production rows and all21 accessor sites, followed by full original-source scope packets and NIB-P1..P4 production continuation.


NIZ latest support: all four held CPI/callback units OPEN; 0/13 complete exclusive-guard owners; zero production Pool-consumer rows CLOSED. K086 production reachability/exclusion remains unproved. Ruling (at) adds NO PDA value row: op38 reply remains quantified; native seed/program-id/reply/status/frame forwarding is still required. No runtime or cryptographic trust row changes in NKC.


NJY-B1 retained: raw decoder rows149/152/153/201/203 do not close Box/ProgramError wrapper consumers48/49 or production Pool joins. No authoritative finite production inventory follows. K086 production reachability/exclusion UNPROVED; owner(aj)(a) PENDING.

NKH makes no production Pool promotion or trust-row change. Pool obligations above remain unchanged; 28function occurrences and the off-domain115supplement were admitted. Digest/error are op43/op44 in the coherent SInt2 cohort. RuntimePersistence remains data-only; RuntimeCpiReadonlyEntry7 unused. K086 retained liveness/abort finding; production reachability/exclusion UNPROVED. Owner(aj)(a) PENDING.
