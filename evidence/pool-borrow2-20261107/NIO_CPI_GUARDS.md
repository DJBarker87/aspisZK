# NIO guards across CPI and callbacks

Status labels concern liveness and borrow safety; no successful transaction, panic reachability, exploit input or transaction shape is claimed. No site is yet discharged. RuntimeCpiReadonlyEntry7 is unused. Data and lamport cells are distinct.

## programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1

Guarded cells: data(accounts[1]): lane_data; data(accounts[2]) if fresh/same; data(accounts[3]) if rollover: page_data.

Passed account positions: token_start + [1,0,3,2,4], token_start=3 or 4.

Actual source checks: pair_forest.rs:1080 exact count; pair_forest.rs:1081 require_unique_accounts(all accounts); vault.rs:355 exact_transfer_account_infos_v1.

OPEN: Actual reached caller layout/key-to-physical-cell relation; callee/CPI frame on that same state; native/meta list association; callback instantiation coverage where applicable.

## programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1

Guarded cells: data(accounts[2]): lane_data; data(accounts[3]) if genesis/same; data(accounts[4]) if rollover: page_data; data(accounts[cursor]): marker_data, cursor=4 or 5.

Passed account positions: token_start + [1,0,2,3,4], token_start=cursor+7.

Actual source checks: pair_forest.rs:1307 require_unique_accounts(all accounts); pair_forest.rs:1285..1318 exact layout; vault.rs:570 exact_withdrawal_transfer_account_infos_v1.

OPEN: Actual reached caller layout/key-to-physical-cell relation; callee/CPI frame on that same state; native/meta list association; callback instantiation coverage where applicable.

## programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1

Guarded cells: data(accounts[current_index or next_index]): history_data, selected index < marker_index; data(accounts[0]): pool_data; data(accounts[marker_index]): marker_data.

Passed account positions: proof_index+1 + [1,0,2,3,4], proof_index=marker_index+4.

Actual source checks: pair_processor.rs:464 require_unique(all accounts); pair_processor.rs:99..178 plan_layout; vault.rs:570 exact_withdrawal_transfer_account_infos_v1.

OPEN: Actual reached caller layout/key-to-physical-cell relation; callee/CPI frame on that same state; native/meta list association; callback instantiation coverage where applicable.

## programs/aspis-pool/src/transition.rs::apply_authorized_append_after_checked_state_v1

Guarded cells: data(pool_account): pool_data; data(current_page_account) if mutate_current: current_data; data(supplied_next_page) if present: next_data.

Passed account positions: Callback-dependent: deposit transfer-info helper; withdrawal marker classifier/creation CPI, token CPI, delta validation, marker write; no-op private-transfer callback..

Actual source checks: transition.rs:735 before_persist; transition.rs:755..864 wrappers forward callback; deposit.rs:163 and 202 require_disjoint_account_groups; processor.rs:2311..2361 withdrawal callback.

OPEN: Actual reached caller layout/key-to-physical-cell relation; callee/CPI frame on that same state; native/meta list association; callback instantiation coverage where applicable.

The three direct CPI layouts have disjoint account-index sets at source level after their actual uniqueness checks. This is not by itself physical-cell separation or a native certificate. The callback cannot be treated as a single zero-effect child: it includes deposit, withdrawal, and no-op instantiations; withdrawal may create the marker before its token CPI. A generic callback type is not a footprint law. No observed-error-arm classification is asserted without a native exact Result certificate.

## Native campaign result and exact gap

All four sites remain OPEN. K002..K021 give ten conditional helper windows with matched controls, but their exact-five validator is a projection stub whose actual uniqueness-loop packet is not closed. K026..K041 give eight unchanged constructor-literal windows with matched controls. These are local input facts, not a native call certificate at any of the four actual reached sites. Their harness payload buffers are small: helper cells contain one byte; constructor payload Vec has one opaque byte while production transfer payloads contain ten. A payload-independent/source-carrier bridge is still required; these restrictions are NOT adopted caller preconditions.

Additionally prove token_accounts[4].key equals the invoked LEGACY_SPL_TOKEN_PROGRAM_ID after the actual token-program validator; the constant program ID is a separate invocation input from the four metas. Source key/cell consistency, checked-list bounds, successful uniqueness and key preservation through prior callees must hold on the same reached state. Bind generic R to the deployed SolanaPoolCpiRuntimeV1 and enumerate each deployed before_persist instantiation; an arbitrary runtime implementation or closure can retain account handles outside its arguments.

No invocation stub has been certified here, and no runtime reply law is silently used. RuntimeCpiReadonlyEntry7 remains unused. The native retained-loop error job and a separate wrong-target control time out; neither is an observed production/CPI error arm.
