# NDR-authoritative cohort reconciliation

**STOPPED in Stage 1:** the first mechanical rebuild failed before elaboration. Zero modules rebuilt; 510 remain. Fifteen unaffected modules were fingerprint-checked and copied privately. No READY.json exists. The hash/source preflight passed, but its per-file path check did not model Lean namespace-root selection; the failed launch exposed that gap. Stage 2 aggregation is not authorized and has not run.

Branch: `codex/pv-evhc-20261029`; worktree: `/Users/dominic/ZK/.worktrees/pv-evhc`.
Consumer: `PV_EVH_FixtureConsumer`; frozen source SHA-256 `2861d5b5b538dde3d821647a5175529b169b248386de6868be0bd05e74d314e4`.

Under D509 / (h6'), the authoritative cohort is `/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects`, used read-only. Its exact committed manifest is `evidence/pv-evhc-20261029/NDR_FINAL_COHORT_PINS.json`, SHA-256 `cbd00ba461b8b8e683d15eaf460e1d317ddedf55b2b5e2309e4fcf2b6d035dd8`. The final NDR output is pinned separately by `NDR_FINAL_OUTPUT_PINS.json`.

`source-identity.json` records all 118 source comparisons: 94 project sources, including `R1FirstFold` at `docs/research/100bit-spend-path-20261013/lean/FirstFold.lean`, and 24 external sources. Project source blobs are identical at `b51b1040f2` and `06f74c902f` and match the predecessor's selected source hashes. External tracked snapshots are byte-identical at both revisions; host preflight checks the actual external source against those common snapshots. The five relevant dependency manifests/toolchain records are identical. No source or proof is edited.

The actual consumer imports `PV_EVH_Deployed`, `PV_RJ4IDB_CallerLive`, and `NDR_CombinedAudit`. The preceding event-headline manifest omitted CallerLive, so this task extends its closure using the committed rj4idb module receipts, build plan, and source-resolution records. An object-header graph determines whether each event-only module transitively imports a conflicting module, including paths through shared modules whose own object hashes agree. A source-import-only preliminary graph is superseded by that binary graph.

New outputs and copies are staged only in `/home/dombarker/project-offloads/codex-pv-evhc2-20261029/`. The normal `S2W_lean_host.py` and `S2W_run_host.py` are copied unchanged from the existing fixture runner. Each mechanical rebuild receives its own ID in 71000–71999, receipt, and scope (MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -M7000). The wrapper checks both fresh admission exit 0 and allowed:true, enforces 180-second refusal cooldowns, refuses failed source resubmissions, and stops on failure or mandatory resource review. Proof-attempt IDs 70900–70999 remain unspent.

Preflight metadata corrections are recorded separately. No Lean was launched during them. One overly broad ID scan was stopped before any compilation and narrowed to job-root runner outputs and receipt trees, avoiding source/dependency caches.

No premise has been removed, added, or changed. The privacy endpoint remains unestablished. FixturePdaRuntime, the event acquisition/joint simulation links, native associations, allocator/abort conditions and the compiler boundary remain as in the predecessor report. Consumer compilation and all consumer `#print axioms` queries await separate lead authorization.

## Attempt 71000 and isolated obstruction

`R0Z.MaskedProtocol` failed with exit 1 after 0.20809789700433612 seconds; peak RSS 189,912 KiB; swaps 0. Its exact source SHA-256 is `52296849b8b85dde21228a42ce7fa97fe1ba92f14a1d1a241f3d71bcae09d989`; original source revision `8b3dc105f492f3a38f1bc9307e5adaf24ad4e5c7`; job plan/tool revision `2e3a5fe870`. This was one uncharged mechanical attempt, no proof attempts. The runner receipt, full error, time log, admission receipt and launch log are retained. Admission exited 0 with allowed:true; the receipt verifies 6G/8G/swap 0/TasksMax 64. No refusal, cap change, OOM, timeout, or retry occurred. `#print axioms`: none executed; import loading failed before elaboration.

Lean reported:

```
object file '/home/dombarker/project-offloads/codex-pv-evhc2-20261029/objects/Mathlib/Data/Real/Basic.olean' of module Mathlib.Data.Real.Basic does not exist
```

The authoritative NDR object exists and hashes to `8097d6032476af4520f0c0a08f69eb04c7adbdedb5fc0e719af580878d817d6e`, matching its committed pin. This is an environment/import-path failure, not a source-law, theorem, or source-identity failure.

`isolation.json` pins the host's Lean/Util/Path.lean implementation: `SearchPath.findWithExt` selects the first root containing the top-level namespace directory, then forms the full module path there. It does not fall back per missing individual object. Copying the permitted reused `Mathlib.Data.FinEnum` created a partial new Mathlib root, shadowing NDR's complete Mathlib root. The inherited normal runner's direct-object fingerprint logic searches individual existing files, so it did not catch the transitive root-shadowing failure. Partial R1Z/R0Z roots present the same risk.

The exact attempted LEAN_PATH was:

```
/home/dombarker/project-offloads/codex-pv-evhc2-20261029/objects:/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028/objects:/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean
```

Per the user's explicit failed-module stop, all compile work stopped after this single failure. No environment repair or resubmission was performed. D490/(u') classifies a later recorded environment correction as changed input, but it does not erase this failure or authorize bypassing this task's stop.

The next concrete deliverable is a reviewed private namespace overlay that resolves every shared module to the authoritative NDR artifact and companions under Lean's actual top-level-root rule. It must never compile through a symlink into NDR. Verify that effective closure first; then any separately authorized changed-environment attempt needs a fresh receipt/ID and an explicit environment diff. There is no completed reconciled cohort manifest yet, and no basis for READY.json or aggregation admission.

The authoritative NDR directory and every Stream A directory remained read-only. All repository writes are confined to the two permitted pv-evhc2 directories. No push.
