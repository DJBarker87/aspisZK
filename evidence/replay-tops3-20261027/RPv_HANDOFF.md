# RPv coherent replay handoff

Branch codex/cx-replay-tops3-20261027. Local commits only, no push. The adopted task top is AspisR1.FJv_Top.deployed; FJv_Deployed remains a non-adopted replay target. Replay removes/adds/changes zero premises (T0/P0/G0/C0). The deployed 100-bit target is not yet established by this job.

## Stage 1 — FJv_Top complete; L187 bookable

All 414 remaining source contexts and the fresh root compile pass on the exact retained RPu/RPt/RPz8/RPz7/trusted cohort. The root header traversal matches every planned context, with no missing or extra selected context. Historical planning counts 6439 contexts: 6438 repository modules plus pinned Mathlib.Tactic.Abel (see RPv_FJv_Top-import-closure-check.json). No source substitution, package replay, predecessor overwrite or predecessor cleanup occurred. All 1005 prepared snapshots are import-only (RPv_source-check.json).

The complete untruncated kernel statement is byte-identical to evidence/stack1-20261027/FJv_after_top.kernel.lean.txt: SHA256 4aff3c961d74a9129413d3430040f3a8258c0139dc686f0851b23c8042af8fee. RPv_FJv_Top.kernel.lean.txt, kernel-expr.json and statement-comparison.json retain the fresh evidence. Only propext/Classical.choice/Quot.sound occur. All 180 formatter records are present and unreachable, including all 84 actual formatter axioms, per record in RPv_FJv_Top-formatter-records.json. Formatter and write_str remain reachable trusted library constants; this is root unreachability, not an all-corpus standard-only claim.

Five declaration batches audit all 414 fresh contexts with 2584 structured declaration queries and matching raw #print axioms lines; no nonstandard axioms or missing context (RPv_axiom-audit.json). Unchanged predecessor declaration audits are reused after pin checking. No new theorem premises are removed by replay. L187 is bookable for FJv_Top on this pinned cohort.

| Target | Attempt | Exit | Wall seconds | Peak RSS KiB | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
| RPv_FJv_Top | RPv_0414 | 0 | 3.481228724005632 | 5736540 | 0 | 50221ac1aedeb631c233adff47402189c9adfe18 |
| RPv_FJv_TopAudit | RPv_0415 | 0 | 18.83505667198915 | 6141960 | 0 | 50221ac1aedeb631c233adff47402189c9adfe18 |
| RPv_AuditBatch01 | RPv_0416 | 0 | 22.410615121014416 | 5530444 | 0 | 50221ac1aedeb631c233adff47402189c9adfe18 |
| RPv_AuditBatch02 | RPv_0417 | 0 | 17.55512827797793 | 3907008 | 0 | 50221ac1aedeb631c233adff47402189c9adfe18 |
| RPv_AuditBatch03 | RPv_0418 | 0 | 19.83740246295929 | 5601828 | 0 | 50221ac1aedeb631c233adff47402189c9adfe18 |
| RPv_AuditBatch04 | RPv_0419 | 0 | 20.741617866966408 | 5667624 | 0 | 50221ac1aedeb631c233adff47402189c9adfe18 |
| RPv_AuditBatch05 | RPv_0420 | 0 | 7.307474920991808 | 5769120 | 0 | 50221ac1aedeb631c233adff47402189c9adfe18 |

Stage 1 uses 420/1100 Lean attempts, all pass; 0 Kani. Aggregate compiler wall 1224.4227096819086 seconds; maximum RSS 6177928 KiB; swaps 0; reservation retries 0. Every attempt has command, source SHA/revision, selected dependency hashes, exit/wall/RSS/swap/cgroup limits and full axioms lines in RPv_attempts.jsonl and raw receipt/output/time logs.

## Resource and pin notes

One scope at a time, MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -j1 -M7000. Reservation logs precede source upload. Same pinned workspace /home/dombarker/project-offloads/codex-cx-replay-dry-20261026; exact ordered LEAN_PATH in each receipt and RPv_PIN-NOTES.md. Initial inherited check passes all 3598 paths. The stage seal detects the lead's external one-line reservation-script correction (quiet refusal exit 0 -> 78); RPv_reservation-tool-transition.json reconstructs the exact old hash from the observed script and records the new hash. All admissions were allowed. No worker edits to host infrastructure; no proof source/compiler/cache substitution. RPv_initial-seal-mismatch.json preserves that detection; RPv_verification.json records the explicit re-pin check. A local dependency-config preflight and a concurrent receipt read stopped without Lean invocation; postprocessing also required narrowing its root selector. No compiler failure or unchanged failed retry occurred.

No shipped Rust/cfg(kani), source adoption, ELF, wallet or key changes. Conditional ELF rebuild trigger does not fire; inherited default f8c0ec72…, devnet 63ad3e9c…, Pool 121f3e29… pins are in RPv_ARTIFACT-SCOPE.md, not newly reproduced. Runtime/game/frozen3/D188 trust decisions and remaining deployment/source-to-ELF obligations are unchanged.

## Stage 2 — pending

591 additional source contexts remain for FJv_Deployed, then its fresh root/kernel/axiom/formatter gates and six declaration batches. Continue on the same cache, one scope at a time; do not delete predecessor objects. Budget remaining after stage 1: 680 Lean attempts, 0 Kani.
