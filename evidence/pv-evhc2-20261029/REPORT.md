# NDR-authoritative cohort reconciliation

Stage 1 preflight passed; 510 event-only modules require rebuilding and 15 may be reused after fingerprint checks. Rebuilds are pending. Stage 2 aggregation is not authorized and has not run.

Branch: `codex/pv-evhc-20261029`; worktree: `/Users/dominic/ZK/.worktrees/pv-evhc`.
Consumer: `PV_EVH_FixtureConsumer`; frozen source SHA-256 `2861d5b5b538dde3d821647a5175529b169b248386de6868be0bd05e74d314e4`.

Under D509 / (h6'), the authoritative cohort is `/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects`, used read-only. Its exact committed manifest is `evidence/pv-evhc-20261029/NDR_FINAL_COHORT_PINS.json`, SHA-256 `cbd00ba461b8b8e683d15eaf460e1d317ddedf55b2b5e2309e4fcf2b6d035dd8`. The final NDR output is pinned separately by `NDR_FINAL_OUTPUT_PINS.json`.

`source-identity.json` records all 118 source comparisons: 94 project sources, including `R1FirstFold` at `docs/research/100bit-spend-path-20261013/lean/FirstFold.lean`, and 24 external sources. Project source blobs are identical at `b51b1040f2` and `06f74c902f` and match the predecessor's selected source hashes. External tracked snapshots are byte-identical at both revisions; host preflight checks the actual external source against those common snapshots. The five relevant dependency manifests/toolchain records are identical. No source or proof is edited.

The actual consumer imports `PV_EVH_Deployed`, `PV_RJ4IDB_CallerLive`, and `NDR_CombinedAudit`. The preceding event-headline manifest omitted CallerLive, so this task extends its closure using the committed rj4idb module receipts, build plan, and source-resolution records. An object-header graph determines whether each event-only module transitively imports a conflicting module, including paths through shared modules whose own object hashes agree. A source-import-only preliminary graph is superseded by that binary graph.

New outputs and copies are staged only in `/home/dombarker/project-offloads/codex-pv-evhc2-20261029/`. The normal `S2W_lean_host.py` and `S2W_run_host.py` are copied unchanged from the existing fixture runner. Each mechanical rebuild receives its own ID in 71000–71999, receipt, and scope (MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -M7000). The wrapper checks both fresh admission exit 0 and allowed:true, enforces 180-second refusal cooldowns, refuses failed source resubmissions, and stops on failure or mandatory resource review. Proof-attempt IDs 70900–70999 remain unspent.

Preflight metadata corrections are recorded separately. No Lean was launched during them. One overly broad ID scan was stopped before any compilation and narrowed to job-root runner outputs and receipt trees, avoiding source/dependency caches.

No premise has been removed, added, or changed. The privacy endpoint remains unestablished. FixturePdaRuntime, the event acquisition/joint simulation links, native associations, allocator/abort conditions and the compiler boundary remain as in the predecessor report. Consumer compilation and all consumer `#print axioms` queries await separate lead authorization.
