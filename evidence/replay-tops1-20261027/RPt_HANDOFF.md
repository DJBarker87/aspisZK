# RPt coherent new-top replay

**Partial coherent replay; budget exhausted after final audits. S2 / deployed 100-bit target not yet established.**
Branch codex/cx-replay-tops1-20261027; original task text used suffix 20261026.
Local commits only; no push. Original source revision:
34b1c8fd70c608938f324f1fa6b74e98f2471bd0.

## Scope and cache

Continuation of the RPz8 coherent cohort in
`/home/dombarker/project-offloads/codex-cx-replay-dry-20261026`.
No duplicate workspace or package replay. Pinned Lean 4.32.0:
`/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0`.
The ordered LEAN_PATH is:

1. that toolchain's `lib/lean`;
2. host workspace `RPt_overlay`;
3. `RPz8_overlay`;
4. `RPz7_overlay`;
5. `RPz4_trusted`;
6. `RPz_trusted`.

New sources/objects reside in RPt_sources / RPt_objects. Existing S2W runner,
admission script and all predecessor objects are unchanged. RPt_inherited-pins.json
pins the RPz8 handoff, plans, verification, library classification and manifest.
RPt_inherited-object-pins.json and RPt_inherited-host-check.json record 1,663
retained paths freshly rehashed without error. These are a direct predecessor
object/sidecar recheck, not fresh compilation credit or a new full trusted-base
rebuild. The broader RPz8 trusted-base audit remains inherited evidence.

RPt_plan.json records each selected original source hash, import mapping and
root closure. All 729 snapshots differ from their selected committed inputs
only in imports (RPt_source-check.json). No original/session A/other-worker
file was edited. No alternate failed source was substituted.

## Budget and frontier

The authorized 400 attempts are fewer than the 729 new dependency vertices.
BEn was scheduled first to establish one complete root, followed by the
FJp/FJu dependency chain. Query contexts do not inflate source-closure credit.
The final source frontier is 395 new green contexts, zero failed vertices,
334 unbuilt. Continuation cache: 5,655 green source contexts including two
inherited contexts outside these new tops' union. The actual new-root union is
5,987 repository contexts: 5,653 green, 334 unbuilt. This distinction prevents
out-of-closure cache objects from inflating closure credit.

| Root | Closure | Reused | Fresh green | Failed | Unbuilt |
|---|---:|---:|---:|---:|---:|
| FJp_Top | 5,788 | 5,251 | 286 | 0 | 251 |
| FJu_Top | 5,871 | 5,251 | 286 | 0 | 334 |
| BEn_Top | 5,367 | 5,258 | 109 | 0 | 0 |

The exact frontier and every unbuilt vertex are RPt_frontier.json.
Fresh root audits and declaration batches are recorded separately.

BEn's 5,367 repository contexts are green (109 fresh, 5,258 reused), with an
exact checked-header closure match (RPt_BEn-import-closure-check.json).
RPt_110 checks the complete type Expr equals ARX after universe alignment,
and also checks their equality by rfl. Its full canonical kernel statement is
RPt_BEn_Top.kernel.txt: 657,311 bytes, SHA256
a0ff8eb5366d7ae62f2de7245ff482457c974da6ff9ba530d216bfd79f53ac90.
The full #print axioms and an independent checked-constant traversal both yield
only propext, Classical.choice and Quot.sound. All 180 formatter implementation
records are present and unreachable, as are all 84 actual formatter axioms.
The Formatter := Unit definition remains reachable. The retained corpus still
contains the 84 native axioms; an all-declaration standard-only claim for that
entire corpus remains false. No formatter or library implementation changed.
RPt_BEn-formatter-records.json has Boolean reachability for every record.

FJv_Top / FJv_Deployed were absent at planning and at the BEn formatter-audit
checkpoint on the lead's research ref d09a6701bd15b1df38fd982c736509624d5525f5;
RPt_FJv-merge-check.json retains that read-only check. No branch was merged.

**FJp/FJu fresh root statements, axiom audits, formatter reachability and
kernel comparisons against their job evidence are NOT ESTABLISHED here.**
Their source bodies match the original accepted job snapshots except imports
(RPt_job-source-comparison.json), but this does not replace a fresh kernel check.
Their queued complete root audits and original kernel-comparison queries are
included as RPt_FJp_TopAudit / RPt_FJu_TopAudit and RPt_*KernelComparison.
They were not compiled against missing dependencies merely to spend attempts.

## Trust, ledger and non-vacuity

RPt_LEDGER.md records the lead's accepted before/after ledger counts and
separates them from this replay's zero premise-removal delta. Complete source
statements and the pinned FJp_statement-check / FJu_statement-check evidence
are retained. Fresh kernel comparisons must be reported independently.
No changed quantifier, carrier, failure event, metric, frozen3 scope or runtime
trust item is introduced. Conditional non-vacuity is not joint deployment
inhabitation. L166 remains an external deployment-side discharge under the
owner-approved extracted-trace interpretation, with no BEn kernel binder removal.
D188 full producer/source-to-ELF provenance and remaining deployment obligations
are not established by replay.

## Resource and artifact scope

Each attempt uses one admitted systemd scope, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, Lean -j1 -M7000 -DElab.async=false.
Every receipt records target, command, exit, wall, peak RSS, swaps, source
revision/hash, dependency pins, cgroup limits, complete printed axioms/errors.
No Kani/Rust/SBF or shipped-file change; the ELF rebuild trigger does not fire.
Inherited release pins, not reproduced:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

No key or wallet action occurred. No binary/object/archive is committed.

## Completed validation and resource receipts

**400/400 Lean attempts used, all pass; 0 Kani.** Exactly 395 new source
contexts plus one complete root audit and four declaration-audit contexts.
All 395 fresh contexts receive 16,723 structured declaration queries and
matching raw #print axioms results. No missing context, nonstandard axiom,
failed source vertex, timeout, memory kill or unchanged failed compiler retry.
RPt_axiom-audit.json and the raw batch logs retain every query.

Aggregate compiler wall: 2053.948817128374 seconds; maximum per-attempt RSS:
5,917,152 KiB; swaps: 0. One reservation contention retry at RPt_115:
48 GiB already reserved + requested 8 GiB exceeded the safe reservation;
waited 180 seconds, then admission passed. No barrier bypass or cap increase.
These timings exclude SSH, admission, collection and git operations.

The initial job-input path omission is fully retained in
RPt_PREFLIGHT-CORRECTION.md / RPt_build-console.log: two pin-only checks failed
before the ninth compiler invocation. No Lean compilation ran for them.
The path was corrected to include RPz8_overlay. The first eight contexts'
selected dependencies do not change. No host launcher or monitoring was fixed.

| Target | Attempt | Exit | Wall seconds | Peak RSS KiB | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
| RPt_BEn_Top | RPt_109 | 0 | 4.273445229977369 | 5541048 | 0 | e5cb4cb209bc6f6a690f3ca2deffb61825f3e84a |
| RPt_BEnAudit | RPt_110 | 0 | 32.08516286301892 | 5917152 | 0 | e5cb4cb209bc6f6a690f3ca2deffb61825f3e84a |
| RPt_AuditBatch01 | RPt_397 | 0 | 31.623797244974412 | 5592172 | 0 | 2683d6e78d6115b7683bb69fc6e5e6c44e208905 |
| RPt_AuditBatch02 | RPt_398 | 0 | 36.131997301999945 | 5610840 | 0 | 2683d6e78d6115b7683bb69fc6e5e6c44e208905 |
| RPt_AuditBatch03 | RPt_399 | 0 | 23.405437669018283 | 5535636 | 0 | 2683d6e78d6115b7683bb69fc6e5e6c44e208905 |
| RPt_AuditBatch04 | RPt_400 | 0 | 29.2621071980102 | 5551700 | 0 | 2683d6e78d6115b7683bb69fc6e5e6c44e208905 |

RPt_attempts.jsonl indexes all 400 targets, source revisions/hashes, dependency
fingerprints, commands, exits, wall/RSS/swap/caps, complete printed axiom lines,
and full raw output hashes. Individual receipts retain complete dependency pins.

## Next deliverable and booking limit

**Only BEn's new root is ready for the coherent-replay booking here.** FJp and
FJu cannot be booked as fresh coherent root successes from this partial run.
Resume at the exact RPt frontier, starting with ready JFv_TX2_FoldResidue /
JFs_TX2_RawMath (full ready list is in RPt_frontier.json). Reuse all 395 accepted
RPt source objects and the unchanged RPz8 / RPz7 / trusted views. Do not rebuild
unchanged modules. The next worker must use its own prefix for remaining copies
and adjust imports to point to the already-green RPt selections.

RPt_next-gates.json records all 334 remaining source contexts and their hashes,
the prepared two complete root-audit queries, and the original-job kernel
comparison queries. Minimum pending gate budget is 342 attempts: 334 source
contexts (including both roots), two root audits, two kernel comparisons,
four declaration batches. Any subsequently merged FJv scope is additional.

Before/after statement evidence and ledger counts are linked above and in
RPt_LEDGER.md. This run removes/adds/changes **0/0/0** premises; ledger delta
**T0/P0/G0/C0**. The lead's earlier FJp and FJu reductions remain inherited
claims pending this run's unfinished coherent root checks. Positive-query
rejection fixtures are fresh; joint deployed-premise inhabitation remains open.
The security target remains **not yet established**.

## Final pins and cleanup

Final consistency passed: all 729 planned source snapshots and originals match
pins; 2,505 retained tool/object/sidecar paths rehash without error; no default
Lake object directory, no active own compiler/runner. Toolchain executables,
shared libraries, unchanged runner, admission script and pinned formatter
library are RPt_toolchain-pins.json. The 23 inherited module resolutions are
pinned by RPt_inherited-pins.json without changing RPz8's selected sources.

RPt_final-verification.json / RPt_final-object-pins.json record the complete
successful pre-cleanup check. RPt_cleanup.json retains hashes/sizes for the
completed own query-only objects removed after that verification. Accepted
source-context proof objects remain in the shared coherent continuation cache.
RPt_retained-object-pins.json is the exact post-cleanup continuation pin set.
No binary, .olean, ELF or archive is committed. Only RPt-prefixed snapshots,
job scripts and receipts in this evidence directory changed.

Removed query-only artifacts: 5; retained pinned paths: 2500.

Source/structured-evidence whitespace check passes. The full staged check flags
only preserved raw-log formatting: a whitespace-only line in RPt_211-launcher.log
and an extra blank line in RPt_toolchain-pin-console.log. Raw captured bytes
are retained unchanged; RPt_diff-check.json records the exceptions.
