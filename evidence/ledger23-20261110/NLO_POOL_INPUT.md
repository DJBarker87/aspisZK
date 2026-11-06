# Pool physical obligations

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
