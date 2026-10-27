# RPu coherent top replay — final handoff

S2 / deployed 100-bit target **not yet established**. Final receipts and continuation pins are attached. Branch codex/cx-replay-tops2-20261027;
initial revision 21913aab6561ae95a880824d5e406c4e5bf096bd. Local commits, no push.
The task's branch suffix 20261026 differs from the supplied checkout; no branch
was renamed or other worktree touched.

## Scope and exact claims

Continue RPt/RPz8 in the single existing host workspace, reusing their objects.
Budget: 500 Lean attempts, 0 Kani. New source contexts are import-only snapshots;
only RPu-prefixed modules and this evidence directory change. See RPu_plan.json,
RPu_source-check.json, RPu_PIN-NOTES.md and RPu_inherited-source-check.json.
No new premise discharge: T0/P0/G0/C0. Before/after source statements and atomic
ledger recount are RPu_*source-statement.txt / RPu_LEDGER.md /
RPu_ledger-check.json. Conditional non-vacuity is retained without a claim of
joint deployment inhabitation. D188/source-to-ELF and deployment obligations
remain open. This audit does not alter frozen3, the game or RuntimePersistence.

## Cohort and resource pins

Workspace: /home/dombarker/project-offloads/codex-cx-replay-dry-20261026.
Lean 4.32.0: /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0.
Ordered LEAN_PATH: toolchain lib/lean, workspace RPu_overlay, RPt_overlay,
RPz8_overlay, RPz7_overlay, RPz4_trusted, RPz_trusted. All new aliases are unique;
no predecessor view/object is overwritten. The 23 historical module resolution
rulings and pinned Aeneas library base are inherited through RPt's exact pins.
RPu_STATUS.md / RPu_PIN-NOTES.md record the additional prepared-loop and WP
resolution. 2500 retained paths and all 395 retained RPt source originals were
checked without mismatch. Per-attempt dependency pins select this ordered path.

Every invocation uses the unchanged S2W runner, one admitted systemd scope at a
time: MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64; Lean -j1 -M7000
-DElab.async=false. Full target/exit/wall/RSS/swap/revision/source/dependency pins
and #print axioms are in each receipt and RPu_attempts.jsonl. No cap increase or
unchanged failed/timed-out retry is authorized. Reservation logs precede scp.

## Budget limitation known at planning

The source frontier needs 251 contexts for FJp, 334 cumulative for FJu, 901 for
FJv_Top, and 1492 for FJv_Deployed. The union contains 1496 contexts, all selected
from committed sources; some FJu contexts are outside the specialized FJv root.
The approved 500 attempts cannot establish either FJv closure. Planned allocation:
491 fresh source contexts, four root/statement audits, five declaration batches.
Only successfully checked complete roots may be booked for L187.

## Artifact and trust limits

RPu_ARTIFACT-SCOPE.md retains inherited ELF pins. No shipped source or cfg(kani)
harness changed, so no SBF rebuild trigger fires. No wallet/key action occurred.
No object, binary, ELF or archive is committed. Accepted source objects are a
continuation cache; own completed query-only objects were cleaned after the
final pin and audit checks, with hashes retained.

## FJp complete root checkpoint

RPu_251 freshly compiles AspisR1.FJp_Top.deployed (exit 0, 2.85543083504308 seconds,
peak RSS 5665764 KiB, swap 0); exact values/revision are in its receipt.
RPu_252 full kernel/axiom/reachability audit and RPu_253 original-job kernel
comparison pass. Its 5788-context planned and checked-header closures match
exactly. RPu_FJp_Top.kernel.lean.txt is the complete untruncated kernel type;
RPu_FJp_Top.kernel-expr.json is the canonical raw Expr record.
The historical default #check bytes match exactly; that historical text has
ellipses and is qualified accordingly in RPu_FJp_Top-statement-comparison.json.
The complete source statement also matches FJp_after.lean.txt byte-for-byte.
All three standard axioms only. All 180 debug-formatter records are present and
unreachable, as are all 84 actual formatter axioms (per-record booleans in
RPu_FJp_Top-formatter-records.json). The broader retained corpus still contains
those axioms; this is root unreachability, not an all-corpus standard-only claim.
Committed as 13978d5595; no premise-removal credit is added by this replay.

## FJu complete root checkpoint

RPu_336 freshly compiles AspisR1.FJu_Top.deployed: exit 0, wall
2.9110565439914353 seconds, peak RSS 5679528 KiB, swap 0;
source revision 13978d55958bdea9716fdf051dd93cac1c729c0b.
RPu_337 full root audit and RPu_338 original-job structural kernel comparison
pass. The planned and checked-header closures both contain exactly 5871
repository contexts. The complete fresh kernel type is byte-identical to
stack1/FJv_before_top.kernel.lean.txt (SHA256
13b9a331b776cc6a5ba4175fb9b2ff0c26155eabd14d9d956aa8aaaa8bfc9e4b).
Historical default #check bytes also match. The source statement differs from
FJu_after.lean.txt only by its extra trailing blank line, retained explicitly.
Only propext/Classical.choice/Quot.sound occur. All 180 debug-formatter records
and 84 actual formatter axioms are unreachable, per record; the trusted
Formatter type and write_str function remain reachable. Committed a8e62a906b.
The mechanical comparison confirms exactly the native first/chain and global
first/chain hypothesis removals inherited from FJu; replay's new delta is zero.

## Final results

**500/500 Lean attempts used, all pass; 0 Kani.** 491 fresh source contexts,
four complete root/statement audit contexts and five declaration batches. No
failed source, timeout, memory kill, unchanged failed retry, reservation contention
or cap increase. No package replay. Compiler wall excludes orchestration and git.

| Root | Closure | Reused | Fresh green | Failed | Unbuilt |
|---|---:|---:|---:|---:|---:|
| FJp_Top | 5788 | 5537 | 251 | 0 | 0 |
| FJu_Top | 5871 | 5537 | 334 | 0 | 0 |
| FJv_Top | 6439 | 5538 | 487 | 0 | 414 |
| FJv_Deployed | 7040 | 5548 | 487 | 0 | 1005 |

The actual root union has 7044 repository contexts,
6039 green and 1005 unbuilt. The continuation cache
has 6146 green source contexts including inherited out-of-union contexts;
those extras are not closure credit. RPu_frontier.json enumerates every unbuilt
vertex. Minimum continuation is 1018 attempts: 1005 sources, two root audits,
and eleven declaration batches; additional structural comparison/non-vacuity gates
would be additional. No further attempts remain under this job's authorization.

All 491 fresh source contexts receive 5055 structured declaration
queries with matching raw #print axioms lines; no nonstandard axioms or missing
context. Earlier unchanged audits are reused after pin checks. Fresh FJp/FJu root
reachability is per-record in RPu_*_Top-formatter-records.json. The two FJv
reports explicitly record UNKNOWN, not false, for their unbuilt roots. Their
complete historical job types remain pinned; fresh comparisons were not run.

Aggregate compiler wall: 1601.0458958387026 seconds; maximum per-attempt
RSS: 6194664 KiB; swap: 0; reservation retries: 0.

| Target | Attempt | Exit | Wall seconds | Peak RSS KiB | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
| RPu_FJp_Top | RPu_251 | 0 | 2.85543083504308 | 5665764 | 0 | b49c5ca8d7b4737245e54c0d58ca139d2bcd7ade |
| RPu_FJp_TopAudit | RPu_252 | 0 | 11.894615725963376 | 6021396 | 0 | b49c5ca8d7b4737245e54c0d58ca139d2bcd7ade |
| RPu_FJu_Top | RPu_336 | 0 | 2.9110565439914353 | 5679528 | 0 | 13978d55958bdea9716fdf051dd93cac1c729c0b |
| RPu_FJu_TopAudit | RPu_337 | 0 | 12.680146308033727 | 6042620 | 0 | 13978d55958bdea9716fdf051dd93cac1c729c0b |
| RPu_AuditBatch01 | RPu_496 | 0 | 21.449179046961945 | 5550936 | 0 | f76f6d517f87fe78a13c329aafbd70a9ee6c05f8 |
| RPu_AuditBatch02 | RPu_497 | 0 | 18.062341551005375 | 5582880 | 0 | f76f6d517f87fe78a13c329aafbd70a9ee6c05f8 |
| RPu_AuditBatch03 | RPu_498 | 0 | 20.59940953896148 | 5671276 | 0 | f76f6d517f87fe78a13c329aafbd70a9ee6c05f8 |
| RPu_AuditBatch04 | RPu_499 | 0 | 20.01518903503893 | 5706008 | 0 | f76f6d517f87fe78a13c329aafbd70a9ee6c05f8 |
| RPu_AuditBatch05 | RPu_500 | 0 | 19.748424871009775 | 5515352 | 0 | f76f6d517f87fe78a13c329aafbd70a9ee6c05f8 |

## Continuation pins and booking limit

Final verification rehashes 3607 tool/source/object/sidecar paths and all
1496 new source snapshots without mismatch. The exact post-cleanup set is
RPu_retained-object-pins.json (3598 paths; SHA256 6b546137ba76703262bd61b1455e3152c255673641a99d6063892aeaece48cd9).
RPu_final-verification.json / RPu_final-object-pins.json retain the pre-cleanup
check. RPu_cleanup.json records 9 own query-only object removals. Accepted
source-context objects and all predecessor caches remain in the same host workspace.

**FJp and FJu are ready for coherent-root replay booking on this pinned cohort.
FJv_Top and FJv_Deployed are NOT ready for L187 booking.** The source frontier
exceeds the supplied budget; no failed module or source substitution caused the
remaining gap. The root/statement/formatter audits for those roots remain open.
RPu_next-gates.json and the prepared RPu_FJv_*Audit queries give the next exact
deliverable. Retain every predecessor and accepted RPu source object; do not run
a package replay. No new source-adoption or release claim follows from this job.

RPu_git-log.txt retains git log --oneline f458169f7..HEAD at the frontier
checkpoint, pinned by RPu_git-log-pin.json; the final evidence-seal commit is
reported separately. All commits remain local, with no push.

Before/after statements and atomic recount are pinned and linked in RPu_LEDGER.md.
Replay removes/adds/changes **0/0/0** premises: **T0/P0/G0/C0**. The adopted
FJv_Top remains the top under the task; FJv_Deployed remains a specialized
candidate. Conditional owner/non-vacuity evidence is inherited, not a new joint
native/runtime inhabitant. The deployed 100-bit target is **not yet established**.

Post-cleanup recheck: all 3598 retained paths match exact hashes and sizes
(RPu_post-cleanup-check.json). No own compiler/runner remained active. Source,
scripts, statements and structured evidence pass whitespace checks. The full
check preserves four raw-log whitespace findings, explicitly listed in
RPu_diff-check.json; raw captured bytes are unchanged. All changed paths have
the job prefix, and git numstat contains no binary entry.
