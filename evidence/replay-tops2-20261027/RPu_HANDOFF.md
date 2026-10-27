# RPu coherent top replay — running record

S2 / deployed 100-bit target **not yet established**. This handoff is a skeleton
until final receipts and pins are attached. Branch codex/cx-replay-tops2-20261027;
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
continuation cache; own completed query-only objects will be cleaned after the
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
All three standard axioms only. All 180 formatter records are present and
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

Pending final audits; see the live RPu_frontier.json for progress. Missing gates
are not successes, and unbuilt source snapshots give no closure credit.
