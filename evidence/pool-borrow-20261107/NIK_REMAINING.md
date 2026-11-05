# NIK remaining work — incomplete native campaign

No Pool consumer row is CLOSED. The deployed Pool-wide borrow invariant and 100-bit per-attempt target are not established. No production panic reachability is established.

## Exact next native deliverable

Implement the original frozen caller's typed guard / explicit-local-record association, on its actual admitted prestate, without writable statics or layout-word guard fabrication. The library-model operation and the actual Rust SDK Rc/guard must refer to the SAME cell; a safe dummy guard or an independently selected counter is insufficient. Pair the native certificate with a live-guard semantic FAIL control. E001 exhausted the permitted extraction run and rejected opaque AccountInfo, so there is no newly emitted scope body to cite. This rejection does not prove the prescribed direct native/Kani/Lean route impossible.

First independent native member: processor::close_program_account_v1. Certify the data temporary's cleanup before lamports(), both lamport block drops before assign/resize, exact source/refund alias and error domains, with explicit borrow-state interpretation. Its source-scope argument and MIR locations are recorded; its native certificate is absent. Then proceed bottom-up through the remaining functions below.

## Member-by-member missing native packets

- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1: lane_data and page_data remain live across runtime.invoke at 1170 and validate_exact_deposit_delta_v1 at 1171. The delta child borrows source/vault token data. Need SAME-cell disjointness between lane/page and those token accounts plus returning CPI borrow/frame. No claim that all counters are nonexclusive at the CPI is valid. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1: lane_data, page_data and marker_data remain live across optional withdrawal runtime.invoke_signed at 1792 and delta validation at 1793; later writes consume the same guards. Need exact transfer-info footprint disjointness and returning CPI frame, not a blanket no-live-guard assertion. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1: master_data remains live while lane_data Vec collects up to eight RefMut values at 2117. Guards escape the loop body through push; they are not dropped each iteration. Need pairwise cell distinctness and Vec-drop/error cleanup. A one-iteration invariant must track all previously collected cells. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1: master_data remains live during checkpoint acquisition; both survive the two copy operations through function return. Need distinct cell admission for simultaneous acquisition; writes use borrowed slices rather than reborrow account data. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1: The rollover/new-page guard is a statement temporary. The else-arm current_data is scoped through append_roots_unchecked. Later pool/marker copy temporaries end at their statements; checkpoint logging and set_return_data are not account-data accessors. Need child slice footprint/Drop laws and alias frame. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1: history_data escapes the if-expression into a function-scope local. It and pool_data/marker_data remain live across runtime.invoke_signed at 554 and validate_exact_withdrawal_delta_v1 at 560. Need SAME-cell footprint exclusion against vault/destination/authority and CPI post-state. Source key/layout checks require physical interpretation. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/processor.rs::close_program_account_v1: The data fill guard is a statement temporary, ending before lamports() at 258. Destination/account lamports guards coexist inside block 259..267 and drop before assign/resize. Need refund/source cell distinctness for acquisition and data temporary Drop; lamports and data are separate cells. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/processor.rs::process_prepare_settlement_with_runtime_v1: core_plan and each optional shard copy use statement temporaries, with no accessor or CPI between acquisition and matching statement cleanup. Need native copy/error/Drop association and shared-entry frame; loop iterations must preserve all other cells. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/processor.rs::process_settle_prepared_with_runtime_v1: Explicit drops of authorization/source-next/current/pool shared guards precede CPI. core_data and shard_data remain until explicit drops at 1892/1893 before close calls. Data copies are statement temporaries; marker and history aliases with surviving shared plan guards still need exclusion. Borrow scopes are not equivalent to a universal zero-counter invariant. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/processor.rs::create_and_write_marker_v1: The marker data guard follows creation/address children and survives only its copy and function return; no later account accessor/CPI is lexical in this scope. Need source prefix/CPI frame and SDK Drop association. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/processor.rs::process_withdrawal_with_runtime_v1: The marker copy temporary follows successful custody CPI inside the before_persist callback. The enclosing transition helper holds pool/current/next guards during that callback. Need callback footprint and alias admission; a local no-RefMut-before-CPI argument would omit guards held by the parent. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/transition.rs::initialize_pool_accounts_v1: pool_data survives acquisition of page_data; owned mutable slices are passed to encoding/page-write children. Need cell distinctness and child no-escape/frame laws; both guards clean up on error/return. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

- programs/aspis-pool/src/transition.rs::apply_authorized_append_after_checked_state_v1: pool_data plus optional current_data and next_data are all live at before_persist at 735. The callback can CPI and access marker data (withdrawal parent). This is a real cross-function guard-carrying edge. Must prove callback touched-cell footprint disjoint from held data cells on the actual layout. A guard-free child-call invariant is false as stated. Native actual-body/explicit-counter association and matched FAIL are still required; no certificate exists.

## Remaining accessor sites and composition

NIK_OPEN_SITES.md names all seven original data_is_empty sites and their direct callers, plus the five data_len and nine lamports sites. Each needs actual root-to-cut counter room, including aliased handles and preceding child/CPI post-states. NIK_HELD_OBLIGATIONS.json records the exact three CPI and one callback MIR boundaries needing held-cell exclusion. Initialization needs arbitrary retained-Vec prefix state, one native iteration and model induction, not eight independent successful acquisitions.

Root SDK deserialization/counter admission, key-to-physical-cell interpretation, successful parser/layout domain packets, and returning System/token-CPI frames remain explicit boundaries. Pool require_unique_accounts/require_unique are not the CLOSED verifier helper merely because their names or result predicates resemble it. Derive the actual Pool helper's successful key list and then the physical-cell consequence. Child guard-free claims must not erase caller-held guards.

## Budget and under-80-percent disclosure

Used 0/100 Kani, 22/60 L slots (14 Lean compiles, two links, three audit runs, export and two cleanup steps), 1/1 extraction, 1/1 MIR compile. There was no Kani exhaustion, no native timeout and no memory kill. The native per-function stage remains UNATTEMPTED; the whole-budget instruction has NOT been completed. The missing packet table explains why no closure is evidenced, not that further Kani attempts are impossible. Further source-local observations could be attempted; they must not be promoted to the required arbitrary-prefix native certificate or ledger credit without the typed same-cell association. No new Lean algebra theorem alone supplies that native fact. This handoff is explicitly partial.

Retain all budgets not consumed. Do not rerun the unchanged MIR compile, passed proof targets or extraction. Reuse the NIK exports and pinned coherent closure for the next native packets and rebuild dependent targets only when their inputs change. Native source/CPI/SDK interpretation is the next deliverable; no new runtime assumption is authorized by this report.
