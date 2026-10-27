# Source-order correction for the next Pool noninterference proof

The blanket strategy claim that an occupied checkpoint in **every** alternate
writable role rejects before heavy arithmetic is overstated. This is a source
ordering observation, not an accepted-write counterexample or a disproof of
checkpoint noninterference. No source or security contract is changed here.

## AS8D current/rollover page role

Pinned `programs/aspis-pool/src/pair_forest.rs:1006–1088` fetches the master,
lane and current page, then calls `pool_v1_note_commitment`, selects/authenticates
the lane, computes the pair-leaf digest and calls `prepare_deposit_append_v1`
(at1025) **before** inspecting the page's zero/fresh form or calling
`validate_lane_current_page` (at1047/1055). `prepare_deposit_append_v1:919–951`
uses the non-invariant append/tree encoder in the frozen features: the deposit
invariant feature is off. Substituting an occupied192-byte ASC8 into current
page slot2 does not make those preceding calls disappear. Address rejection of
that wrong page also occurs after those calls.

## ASPP core/shard role

Pinned `programs/aspis-pool/src/processor.rs:1218–1270` may create/allocate a
rollover page, then calls `build_prepared_settlement_plan_v1` before the core
plan's `plan_fresh_program_pda` size/freshness check. If the core-plan slot holds
an occupied checkpoint, a later rejection must retain the actual preceding
child/error/effect prefix; the runtime's transaction rollback is a separate
accepted trust item. There is no permission to omit a prior CPI or force an
owned arithmetic child to return success.

## Required proof consequence

Keep the accepted noninterference target unchanged. Prove per-role source cuts:
either an earlier real error/rejection frames the checkpoint, or the reached
size/freshness guard rejects after the **same** actual preceding calls/effects.
Use owned-child footprint/refinement results without proving unrelated field
arithmetic, but keep every Result alternative and ordered effect. Source
framing/absence of account capabilities in such children must itself be joined
to the actual native call. PoolN_Effects.rejected_prefix preserves a supplied
prefix; it does not derive that prefix from the handler. The missing instance
must not be hidden by treating the handler as if its guard were first.

The successful primary-state/payer guard tests and local helper tests do not
resolve these page/plan role prefixes. `PoolN_Frame.all_handlers` is still open.
