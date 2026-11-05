# NIK OPEN sites: production invariant NOT established

All claims here concern liveness/abort correctness. No production reachability counterexample, adversarial inputs or transaction shapes are constructed. K086 is retained on its original domain. No soundness, privacy, per-attempt target or two-transaction claim changes.

## Native/model boundary

The single permitted actual-body extraction NIK_E001 reaches Charon output but Aeneas rejects the opaque AccountInfo carrier: cannot retrieve variants of non-ADT solana_account_info::AccountInfo (Substitute.ml:377..380). Its tool failure is not a native counterexample. The imported NIE library laws are available, but do not identify the actual Rust Rc counter, guard lifetime, caller domain or CPI post-state of these Pool prefixes. No such identification is assumed.

NIK scope_model_invariant is a CONDITIONAL LIBRARY MODEL theorem, not a Pool-wide deployed-path theorem. A ScopeRun instance, root admission, alias interpretation, retained-guard interior sites and returning child/CPI frames remain unproved. Replacing these with a framedChild premise would merely restate the missing obligation. No native per-function certificate is claimed.

## Seven originally requested data_is_empty sites

### programs/aspis-pool/src/nullifier.rs:208 classify_nullifier_marker_account_v1

Derive no live exclusive guard on the same data cell from actual caller prefix, including aliases and preceding callee/CPI frames; native matched-control certificate plus model association required.

Direct caller source sites: plan_nullifier_marker_consumption_v1@178, plan_pair_forest_nullifier_marker_consumption_v1@260, recheck_pair_forest_nullifier_marker_v1@274.

Shared room additionally requires the NIE saturation upper bound on the SAME cell, not just a nonnegative counter. All post-child and post-CPI states must be the actual reached states.

### programs/aspis-pool/src/pair_forest.rs:1031 process_pair_forest_deposit_with_runtime_v1

Derive no live exclusive guard on the same data cell from actual caller prefix, including aliases and preceding callee/CPI frames; native matched-control certificate plus model association required.

Direct caller source sites: process_instruction@2461.

Shared room additionally requires the NIE saturation upper bound on the SAME cell, not just a nonnegative counter. All post-child and post-CPI states must be the actual reached states.

### programs/aspis-pool/src/processor.rs:292 plan_fresh_program_pda

Derive no live exclusive guard on the same data cell from actual caller prefix, including aliases and preceding callee/CPI frames; native matched-control certificate plus model association required.

Direct caller source sites: plan_pair_forest_checkpoint_accounts_v1@771, process_pair_forest_deposit_with_runtime_v1@1035, process_pair_forest_deposit_with_runtime_v1@1063, process_pair_forest_initialize_with_runtime_v1@2017, process_pair_forest_initialize_with_runtime_v1@2031, process_pair_forest_checkpoint_with_runtime_v1@2149, require_fresh_rent_exempt_program_pda@614, process_initialize_with_runtime_v1@657, process_initialize_with_runtime_v1@664, process_deposit_with_runtime_v1@809, create_prepare_rollover_page_if_needed@1126, process_prepare_settlement_with_runtime_v1@1253, process_prepare_settlement_with_runtime_v1@1264, create_next_root_page_if_needed@1943, process_private_transfer_with_runtime_v1@2112, process_withdrawal_with_runtime_v1@2272.

Shared room additionally requires the NIE saturation upper bound on the SAME cell, not just a nonnegative counter. All post-child and post-CPI states must be the actual reached states.

### programs/aspis-pool/src/processor.rs:332 create_or_allocate_pda_with_rent

Derive no live exclusive guard on the same data cell from actual caller prefix, including aliases and preceding callee/CPI frames; native matched-control certificate plus model association required.

Direct caller source sites: create_or_allocate_pda@309, create_nullifier_marker_if_needed_v1@1599.

Shared room additionally requires the NIE saturation upper bound on the SAME cell, not just a nonnegative counter. All post-child and post-CPI states must be the actual reached states.

### programs/aspis-pool/src/processor.rs:398 create_or_allocate_with_seed_with_rent

Derive no live exclusive guard on the same data cell from actual caller prefix, including aliases and preceding callee/CPI frames; native matched-control certificate plus model association required.

Direct caller source sites: create_pair_forest_nullifier_marker_if_needed_v1@1643.

Shared room additionally requires the NIE saturation upper bound on the SAME cell, not just a nonnegative counter. All post-child and post-CPI states must be the actual reached states.

### programs/aspis-pool/src/processor.rs:504 plan_vault_initialization

Derive no live exclusive guard on the same data cell from actual caller prefix, including aliases and preceding callee/CPI frames; native matched-control certificate plus model association required.

Direct caller source sites: process_pair_forest_initialize_with_runtime_v1@2024, process_initialize_with_runtime_v1@670.

Shared room additionally requires the NIE saturation upper bound on the SAME cell, not just a nonnegative counter. All post-child and post-CPI states must be the actual reached states.

### programs/aspis-pool/src/vault.rs:485 plan_legacy_withdrawal_transfer_from_identity_v1

Derive no live exclusive guard on the same data cell from actual caller prefix, including aliases and preceding callee/CPI frames; native matched-control certificate plus model association required.

Direct caller source sites: process_pair_forest_terminal_with_verifier_v1@1697, process_pair_withdrawal_with_verifier_v1@490, plan_legacy_withdrawal_transfer_v1@399.

Shared room additionally requires the NIE saturation upper bound on the SAME cell, not just a nonnegative counter. All post-child and post-CPI states must be the actual reached states.

## All additional emitted infallible accessor sites

These fourteen sites share the same class of precondition. This list is deliberately broader than NIE data_is_empty inventory. Emission of a generic body is not proof of root reachability.

- programs/aspis-pool/src/pair_forest.rs::require_forest_mint_account:392 data_len; data cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [38340].
- programs/aspis-pool/src/pair_forest.rs::require_program_owned_zeroed:410 lamports; lamports cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [38793].
- programs/aspis-pool/src/pair_forest.rs::account_is_zeroed_program_page:810 data_len; data cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [46895].
- programs/aspis-pool/src/processor.rs::close_program_account_v1:248 data_len; data cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [122632].
- programs/aspis-pool/src/processor.rs::close_program_account_v1:258 lamports; lamports cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [122773].
- programs/aspis-pool/src/processor.rs::create_or_allocate_pda_with_rent:342 lamports; lamports cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [124056, 124102].
- programs/aspis-pool/src/processor.rs::create_or_allocate_pda_with_rent:355 lamports; lamports cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [124056, 124102].
- programs/aspis-pool/src/processor.rs::create_or_allocate_with_seed_with_rent:409 lamports; lamports cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [124771, 124818].
- programs/aspis-pool/src/processor.rs::create_or_allocate_with_seed_with_rent:424 lamports; lamports cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [124771, 124818].
- programs/aspis-pool/src/processor.rs::require_fresh_rent_exempt_program_pda:609 data_len; data cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [127265].
- programs/aspis-pool/src/processor.rs::require_fresh_rent_exempt_program_pda:618 lamports; lamports cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [127304].
- programs/aspis-pool/src/processor.rs::require_prepared_plan_account_v1:1471 data_len; data cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [140172].
- programs/aspis-pool/src/processor.rs::create_nullifier_marker_if_needed_v1:1614 lamports; lamports cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [141733].
- programs/aspis-pool/src/processor.rs::create_pair_forest_nullifier_marker_if_needed_v1:1659 lamports; lamports cell. Derive actual incoming counter lower/upper bounds and preceding child/alias frame. MIR candidate lines [142100].

## Exclusive functions: individual missing packets

- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_deposit_with_runtime_v1: lane_data and page_data remain live across runtime.invoke at 1170 and validate_exact_deposit_delta_v1 at 1171. The delta child borrows source/vault token data. Need SAME-cell disjointness between lane/page and those token accounts plus returning CPI borrow/frame. No claim that all counters are nonexclusive at the CPI is valid. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1: lane_data, page_data and marker_data remain live across optional withdrawal runtime.invoke_signed at 1792 and delta validation at 1793; later writes consume the same guards. Need exact transfer-info footprint disjointness and returning CPI frame, not a blanket no-live-guard assertion. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_initialize_with_runtime_v1: master_data remains live while lane_data Vec collects up to eight RefMut values at 2117. Guards escape the loop body through push; they are not dropped each iteration. Need pairwise cell distinctness and Vec-drop/error cleanup. A one-iteration invariant must track all previously collected cells. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/pair_forest.rs::process_pair_forest_checkpoint_with_runtime_v1: master_data remains live during checkpoint acquisition; both survive the two copy operations through function return. Need distinct cell admission for simultaneous acquisition; writes use borrowed slices rather than reborrow account data. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/pair_processor.rs::process_pair_private_transfer_with_verifier_v1: The rollover/new-page guard is a statement temporary. The else-arm current_data is scoped through append_roots_unchecked. Later pool/marker copy temporaries end at their statements; checkpoint logging and set_return_data are not account-data accessors. Need child slice footprint/Drop laws and alias frame. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/pair_processor.rs::process_pair_withdrawal_with_verifier_v1: history_data escapes the if-expression into a function-scope local. It and pool_data/marker_data remain live across runtime.invoke_signed at 554 and validate_exact_withdrawal_delta_v1 at 560. Need SAME-cell footprint exclusion against vault/destination/authority and CPI post-state. Source key/layout checks require physical interpretation. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/processor.rs::close_program_account_v1: The data fill guard is a statement temporary, ending before lamports() at 258. Destination/account lamports guards coexist inside block 259..267 and drop before assign/resize. Need refund/source cell distinctness for acquisition and data temporary Drop; lamports and data are separate cells. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/processor.rs::process_prepare_settlement_with_runtime_v1: core_plan and each optional shard copy use statement temporaries, with no accessor or CPI between acquisition and matching statement cleanup. Need native copy/error/Drop association and shared-entry frame; loop iterations must preserve all other cells. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/processor.rs::process_settle_prepared_with_runtime_v1: Explicit drops of authorization/source-next/current/pool shared guards precede CPI. core_data and shard_data remain until explicit drops at 1892/1893 before close calls. Data copies are statement temporaries; marker and history aliases with surviving shared plan guards still need exclusion. Borrow scopes are not equivalent to a universal zero-counter invariant. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/processor.rs::create_and_write_marker_v1: The marker data guard follows creation/address children and survives only its copy and function return; no later account accessor/CPI is lexical in this scope. Need source prefix/CPI frame and SDK Drop association. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/processor.rs::process_withdrawal_with_runtime_v1: The marker copy temporary follows successful custody CPI inside the before_persist callback. The enclosing transition helper holds pool/current/next guards during that callback. Need callback footprint and alias admission; a local no-RefMut-before-CPI argument would omit guards held by the parent. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/transition.rs::initialize_pool_accounts_v1: pool_data survives acquisition of page_data; owned mutable slices are passed to encoding/page-write children. Need cell distinctness and child no-escape/frame laws; both guards clean up on error/return. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.
- programs/aspis-pool/src/transition.rs::apply_authorized_append_after_checked_state_v1: pool_data plus optional current_data and next_data are all live at before_persist at 735. The callback can CPI and access marker data (withdrawal parent). This is a real cross-function guard-carrying edge. Must prove callback touched-cell footprint disjoint from held data cells on the actual layout. A guard-free child-call invariant is false as stated. The missing packet is an actual-body native scope/child certificate and same-prefix model association, not another scalar cleanup identity.

## Slice boundaries

SDK entrypoint/deserialization -> Pool physical entry/counter admission; AccountInfo RefCell carrier/Drop interpretation; System and token CPI returning account/counter footprints; generic runtime and before_persist concrete instantiation/borrow footprints. Source/MIR census retains generic dispatch as unresolved and does not import a guessed runtime row. Key inequality alone does not prove physical-cell inequality. No RuntimeCpiReadonlyEntry7 premise is used.
