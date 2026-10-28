# Stage 2: exact live iteration and afterstate Result

Established on the coherent SInt2 carriers: NBK_SliceStore.exact (generic slice copy/back with exact width and bounds), NBK_LiveStep.body_done/body_write (the actual live codec iterator body), NBK_LiveBytes.loop_exact (all remaining rows by symbolic induction, arbitrary 800-byte pre-state), and NBK_AfterstateResult.source (full emitted afterstate Result for every typed record, no validation/canonicality premise; reuses NBH validator and S2K bytes). NBD/NBH modules are imported unchanged.

K001-K007 pass exact fixed-position 32-byte writes and full byte frames, arbitrary output/source bytes. They replace seven of the retired dynamic-store positions; other positions are still pending. No unchanged timeout rerun. Each has fresh admitted serial capped scope, optimized offline Kani, frozen graph/lock preflight and unchanged lock afterward. No stubs or field multiplication in these native stores.

L003/L005/L006/L007/L011 are new passing roots; only standard axioms. Failed inspection/drafts and missing-import attempts retained. L008/L009/L012-L016/L019/L021-L026 compile missing unchanged dependencies once into the designated persistent cache; source copies and hashes/revisions are retained in receipts. Existing cache entries are not overwritten. This is focused dependency reuse, not final release replay.

S6 callback audit NBK_CallbackSelection confirms registry and policy/account slots are retained from input adapter data; not installed concrete implementations. The full SDK selection audit is still pending. No new dictionary, source association or premise removal is claimed from it.

U03/U04/U05 remain OPEN and the deployed target is not established. Frozen Rust/programs diff is empty against 4bb3b3f5. No worktree shipped code, keys or release ELFs changed. Inherited ELF hashes were not rebuilt. Further work: complete native row positions, full live/prefix byte law, ASF8 ordered preflight and U04 sequence iterations; retain exact lower codec dependencies.

L027 additionally proves NBK_LivePrepare.exact, the emitted fixed-prefix action on arbitrary 800-byte slices, reusing JFt_SnapshotConstants.format_call. L028 proves NBK_DeployedCallbackSelection.registry/policy_accounts on the actual DrvC_Installation.sdk configuration, with no new dictionary. The additional missing unchanged Port4/Port5/Op4 dependencies were built once with serial scopes (exact sources in receipts). These selection facts expose unresolved adapter data and make no whole-source or premise-removal claim.
