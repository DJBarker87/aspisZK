# NLG physical association distances

Target not yet established. Fourteenth all-slices composition test. Distances count remaining conditional native/source associations under NDT semantics; they are not runtime measurements or headline soundness. No edge is pruned.

| Part | Total | CLOSED | OPEN | QUALIFIED |
|---|---:|---:|---:|---:|
| (ao)(3)(b) | 53 | 40 | 13 | 0 |
| (ao)(3)(c) | 546 | 524 | 22 | 0 |

## Shortest OPEN spines

Same targets as NKW: TX1 entry330→driver094, TX2 entry213→finish115. BFS minimizes canonical call edges and counts OPEN rows along the selected spine; CLOSED child rows do not promote an unsubmitted parent. Conservative069→202 remains.

TX1: TX1:330 process_r1_cost_probe_instruction [OPEN] → TX1:333 process [OPEN] → TX1:344 stage1 [OPEN] → TX1:345 stage1_owned [OPEN] → TX1:328 first_decoded [OPEN] → TX1:094 tx1 [OPEN]. OPEN distance 6; 5 call edges.

TX2: TX2:213 process_r1_cost_probe_instruction [OPEN] → TX2:221 process [OPEN] → TX2:240 stage2 [OPEN] → TX2:241 stage2_owned [OPEN] → TX2:064 tx2_authenticated [OPEN] → TX2:065 tx2_common [OPEN] → TX2:115 finish_relation [CLOSED]. OPEN distance 6; 6 call edges.

## OPEN rows by source file and live job

### crates/aspis-r1-cost-probe/src/candidate.rs

| Row | Function | Live owner |
|---|---|---|
| TX1:081 | batch_merkle | NKV_ batch-merkle4 |
| TX1:082 | batch_merkle_values | NKV_ batch-merkle4 |
| TX1:083 | batch_tree | NKV_ batch-merkle4 |
| TX1:087 | prepare | NLC_ tx1-driver2 |
| TX1:094 | tx1 | NLC_ tx1-driver2 |
| TX2:053 | batch_merkle | NKV_ batch-merkle4 |
| TX2:054 | batch_merkle_values | NKV_ batch-merkle4 |
| TX2:055 | batch_tree | NKV_ batch-merkle4 |
| TX2:064 | tx2_authenticated | NLE_ tx2-entry |
| TX2:065 | tx2_common | UNOWNED; lead routing required |

### crates/aspis-r1-cost-probe/src/r1_semantic.rs

| Row | Function | Live owner |
|---|---|---|
| TX1:136 | verify_finish | NLC_ tx1-driver2 |
| TX1:137 | verify_observed | NLC_ tx1-driver2 |

### crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs

| Row | Function | Live owner |
|---|---|---|
| TX1:218 | evaluate_with_selectors | NKR_ terminal5 |
| TX1:220 | finish_selector_tensor_basis | NKR_ terminal5 |
| TX1:225 | qm31_sum_products_up_to4 | NKR_ terminal5 |

### crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs

| Row | Function | Live owner |
|---|---|---|
| TX1:232 | add_schedule_lanes | NKR_ terminal5 |
| TX1:237 | composition_parts | NKR_ terminal5 |
| TX1:250 | public_digest_packed | NKR_ terminal5 |
| TX1:251 | public_digest_packed_selector_tensor | NKR_ terminal5 |
| TX1:256 | r0::Public<'a>::terminal_qm31 | NKR_ terminal5 |
| TX1:261 | semantic_packed | NKR_ terminal5 |
| TX1:263 | terminal_parts | NKR_ terminal5 |

### programs/r1-cost-probe/src/lib.rs

| Row | Function | Live owner |
|---|---|---|
| TX1:328 | first_decoded | UNOWNED; lead routing required |
| TX1:330 | process_r1_cost_probe_instruction | UNOWNED; lead routing required |
| TX2:213 | process_r1_cost_probe_instruction | NLE_ tx2-entry |

### programs/r1-cost-probe/src/r1_pool_adapter.rs

| Row | Function | Live owner |
|---|---|---|
| TX1:333 | process | UNOWNED; lead routing required |
| TX2:217 | decode_lane_from_pool_release | UNOWNED; lead routing required |
| TX2:221 | process | NLE_ tx2-entry |

### programs/r1-cost-probe/src/r1_pool_adapter_owned.rs

| Row | Function | Live owner |
|---|---|---|
| TX1:344 | stage1 | UNOWNED; lead routing required |
| TX1:345 | stage1_owned | UNOWNED; lead routing required |
| TX2:233 | authenticate_asq8_accounts | UNOWNED; lead routing required |
| TX2:234 | authenticate_invariant_release_registry | UNOWNED; lead routing required |
| TX2:240 | stage2 | NLE_ tx2-entry |
| TX2:241 | stage2_owned | NLE_ tx2-entry |
| TX2:242 | validate_asq8 | UNOWNED; lead routing required |

## Unowned OPEN rows

TX1:328, TX1:330, TX1:333, TX1:344, TX1:345, TX2:065, TX2:217, TX2:233, TX2:234, TX2:242. NKO_, NKQ_, NLA_, NLB_, NLD_ and NKX_ are supporting evidence, not new gated candidates or live row ownership in this job. NLF_ sdk-borrow supplies shared support for entry rows and Pool guard owners; it closes no row here.

## Native input clauses

TX2:124 closes only within proof57607/public0..1880 native scope. TX2:065 and upward064/241/240/221/213 retain that OPEN obligation at SAME resume arguments, including source serialized-public provenance. The broader Lean source equation does not widen native credit. TX1:251 retains235 canonical frontier/opening/high domain and semantic-public context. All original NKW clauses remain recorded.

## (ao)(3)(d): named Pool obligations

Pool revision b936275465600469312d1f058cdc91ea2a11f3dc, ELF e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc; historical121f3e29… is superseded for Pool only. No verifier row depends on Pool ELF. The599 verifier basis is unchanged; zero production Pool-consumer occurrences are credited. Three inherited CLOSED helper entries (pair_forest_dispatch.supported_loader, processor.require_transaction_level_invocation_v1, error.convertPoolError) are not whole-Pool closure.

NKZ inventory only:397 ON occurrences,278 new to basis,119 shared bodies matching183/599, D30. Six retained exclusive owners(3 ON/3 OFF), three held sites(2 ON/1 OFF), all OPEN;15 accessors, seven data_is_empty sites. No native closure follows from body matching or legacy deletion.


Target not yet established. Inventory only; all retained held sites and exclusive-guard scopes remain OPEN; removed sites/owners are listed in NKZ_DIFF.md. NKZ_OBLIGATIONS.json retains every unresolved/SDK/std/indirect call with artifact and line, all current accessor sites, all owner source events, and numbered P1..P4 producers.

| Held site | Numbered occurrence / scope | Exact guarded and passed layout |
|---|---|---|
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1` | POOL:328 ON_CONSERVATIVE_CLOSURE | guards1/2 fresh/same or1/3 rollover; passed token_start+[1,0,3,2,4], token_start3/4 |
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1` | POOL:330 ON_CONSERVATIVE_CLOSURE | guards2/3 genesis/same or2/4 rollover plus marker cursor4/5; passed cursor+7+[1,0,2,3,4] |
| `programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1` | POOL:400 OFF_REVIEW_NOT_ON_CLOSURE | guard pool0, selected history<marker and marker; passed proof_index+1+[1,0,2,3,4], proof_index=marker+4 |

The ASJW pair-withdrawal site is retained OFF because its dispatcher feature is absent. It is not evidence of an ON reached panic. Two held units remain in the ON union; the legacy transition callback was deleted. The checkpoint root remains ON; legacy close/cancel/prepared settlement were deleted.

| Exclusive owner | Row / scope | Required next packet |
|---|---|---|
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1` | POOL:328 ON_CONSERVATIVE_CLOSURE | exact_transfer_account_infos_v1; deployed SolanaPoolCpiRuntimeV1::invoke |
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1` | POOL:330 ON_CONSERVATIVE_CLOSURE | plan_pair_forest_spend_layout_v1; exact_withdrawal_transfer_account_infos_v1; deployed verify/settle instantiations |
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1` | POOL:398 OFF_REVIEW_NOT_ON_CLOSURE | prepare_fresh_program_pda; actual retained lane-guard loop |
| `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1` | POOL:327 ON_CONSERVATIVE_CLOSURE | prepare_fresh_program_pda; decode/encode checkpoint and persistence suffix |
| `programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1` | POOL:399 OFF_REVIEW_NOT_ON_CLOSURE | deployed verifier invocation; apply_pair_private_transfer_after_state_v1 |
| `programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1` | POOL:400 OFF_REVIEW_NOT_ON_CLOSURE | require_unique; exact_withdrawal_transfer_account_infos_v1; marker/verification/token children |

| Composition obligation | Numbered producers | Remaining association |
|---|---|---|
| POOL.prefix_to_cpi | POOL:322, POOL:329, POOL:330, POOL:347, POOL:348, POOL:350 | Actual accepted prefix, exact selected CPI/meta/payload and live guards. |
| NIB-P1 | POOL:344, POOL:345, POOL:347, POOL:348 | SAME CPI emission/program/context, immediate read and exact no-intervening-register-write frame. |
| NIB-P2 | POOL:311, POOL:312, POOL:313, POOL:314, POOL:339 | Actual validation dictionary, every Result/error arm and SAME request/master/checkpoint/lane/result. |
| NIB-P3 | POOL:319, POOL:320 | Actual lane dictionary and SAME state/carriers/image. |
| NIB-P4 | POOL:330 | Complete settlement/withdrawal/account write, borrow, mutation and cleanup frame. |
| POOL.read_to_settlement | POOL:311, POOL:312, POOL:313, POOL:314, POOL:319, POOL:320, POOL:330, POOL:339, POOL:344, POOL:345, POOL:347, POOL:348 | Conditional NIB theorem retained; all P1..P4 production producers remain uninstantiated. |

RuntimeEntrypointAdmission-Pool (ap) supplies valid/freshGuards/noExternalBorrows/liveAccount/counterZero/sharedCellsOnlyEqualKeys/duplicateKeysShareCell at initial entry only. It repairs the former missing entry premise. Caller uniqueness, reached layouts and preservation to the CPI remain to prove. S2TrustedSdkBorrow covers fifteen data-only fields; Rc clone/free, lamport borrows, assign/resize, CPI/reentrancy and token behavior are outside it. RuntimePersistence is data-only across the two transactions.

RuntimeReturnData covers nonempty1..1024; RuntimeReturnDataClear covers empty clears. Neither supplies SAME invocation, selected program or caller register continuity. Clock binding covers slot only. RuntimeSha256Value supplies H realization, while native request/reply association remains. PDA op38 is quantified under(at), with seed/program/status/frame forwarding still required; no new PDA value trust.

RuntimeCpiReadonlyEntry7 is PENDING and UNUSED. CPI/system/token program effects, Rent realization, stack-height value binding, lamport/assign/resize and Rc behavior have no blanket accepted row: NONE: would need a new trust row (owner decision) **if assumed**; a proof route can discharge them instead. This report proposes no such addition.

K086: NHP_K086, `core::cell::panic_already_mutably_borrowed::do_panic::runtime`, core/cell.rs:898, “Kani doesn't support message formatted at runtime”; 1/1024 failed,12 unreachable. Source inspection explains the live-exclusive/System-empty/infallible-borrow mismatch. Production reachability/exclusion remains UNPROVED; it is liveness/abort, not a soundness counterexample.

All current accessor sites are numbered or explicitly OFF in NKZ_OBLIGATIONS.json. No accessor silently inherits initial counterZero at a later call.

### Legacy owner disposition

Seven former guard owners and transition::apply_authorized_append_after_checked_state_v1 held callback were REMOVED SOURCE, not proved: close_program_account_v1, process_prepare_settlement_with_runtime_v1, process_settle_prepared_with_runtime_v1, create_and_write_marker_v1, process_withdrawal_with_runtime_v1, initialize_pool_accounts_v1, apply_authorized_append_after_checked_state_v1. Exact old/new rows and all surviving ON/OFF sites: NKZ_DIFF.md. Original13→6guard owners,4→3held sites,21→15accessors.

Owner(aj)(a) PENDING: same-game settlement optionA versus external Pool-association conditionalB. K086 is liveness/abort; production reachability/exclusion UNPROVED. RuntimeCpiReadonlyEntry7 PENDING/UNUSED. Initial Pool admission seven fields only; no CPI continuation/frame. RuntimePersistence data-only; PDA op38 quantified; digest/error43/44. L154 statement parameter; extraction/P6/D188 option-A retained. No runtime or cryptographic trust changes.
