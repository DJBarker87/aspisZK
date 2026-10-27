> Superseded for the D275 resume by [REPORT-D275.md](REPORT-D275.md).
> Final source `c58e0473ac`: three ELF pins match; extraction now stops at
> `records:238–242`, `InterpBorrows.ml:2731` (unapproved branch-body repair).
> The original runjoin14 report below is retained as historical evidence.

# pv-runjoin14 — copy repair clears borrow; range iterator stops extraction

**Target not yet established. Stage 3 remains open.** Branch
`codex/pv-runjoin-20261026`, entry `9128568ac068bee9527806edc32982a35010c706`.
The only shipped repair is committed at `05cb63a2ea`: inside records,
`let pair = &input.pair;` becomes `let pair = input.pair;`. The Copy derive
is pair_trace.rs:71. See `REPAIRS.md` and `shipped-records.diff`.
All 510 tracked crates/programs/lockfile files in the private host snapshot
byte-match the committed local source (host-source-agreement.json).
No other shipped function/signature/type changed. No shared env-J source write,
merge, push, repin, wallet-key deletion, observer/simulator change or T addition.

## Gate (a)

Gate (a) **PASSED**; all three pins MATCH (gate-a.json).

| Target | Exit | Wall s | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
| default | 0 | 76.309 | 682900 | 0 |
| devnet | 0 | 69.453 | 685512 | 0 |
| Pool | 0 | 75.193 | 678624 | 0 |

Full expected/actual SHA-256 and artifact sizes are in gate-a.json.
Exact commands and metrics for all five host scopes are in receipt-index.json;
Charon exits 0 in 49.077 s, peak RSS 1,344,675,840 bytes; Aeneas exits 2 in
0.710 s, peak RSS 85,467,136 bytes; both report zero swaps.
All builds use the existing private gate13 workspace/cache and unchanged
runjoin13 SBF commands, caps (6G/8G/swap 0, TasksMax 64) and public devnet IDs.
Expected work is optimized SBF compilation; at most one scope from this job.
The source revision is 05cb63a2ea (full in source-revision.txt); the first
build's raw receipt uses this unique short revision, later builds the full hash.
New artifact keys are retained on the host at mode 0600; no key contents are
copied to evidence. Gates (b)/(c) remain lead-owned per runjoin13/GATE-PLAN.md.

## Extraction and stop

`pv14-records-charon-01`: exit 0, clean preflight, records body retained.
`pv14-records-aeneas-01`: exit 2 on unsupported `ub_checks<bool>` in the
inlined range iterator (core/iter/range.rs:984–986, InterpExpressions.ml:1512).
The old records:230 / InterpAbs.ml:1955 borrow blocker has been cleared.
Pinned tools match runjoin13; preflight stays on. Complete commands, source/tool
hashes, diagnostics and resources are committed in the two receipt directories.
These diagnostic extractions preceded the final three-ELF gate; no result is
accepted as a release extraction and no unchanged extraction is rerun.

The minimal source repair for the new blocker is the existing range `for` to
indexed `while` rewrite, preserved **unapplied** in range-loop-proposal.diff.
That iterator-loop rewrite is not a Copy-borrow replacement or one of the
already-authorized closure/combinator removals. D274 explicitly requires this
route to stop. See `BLOCKER.md`, `intrinsic-location.json` and
`extraction-preflight.json`. No extractor patch, stub or assumed source equality
was introduced. This is a failure of the tested pinned configuration, not an
impossibility result for every extraction configuration. The isolated raw helper
also still needs its concrete connection; historical direct FnOnce failure is
retained rather than repeated. No R_shipped definition was accepted.

## Proof and trust status

Transfer identification: OPEN. Withdrawal identification: OPEN. General
identification: OPEN. Compiler-return equation, transition equality at actual
selected i, deployed public binding, and P ∧ T non-vacuity: OPEN.
The 21 proved mathematical empty-root cells and research PV_Src_* reference
results remain retained prior work; no source identification is inferred.
Constructed P remains {source public binding, trace}; deployed P remains OPEN;
record counts 2/8/6 → 2/8/6. Endpoint premises removed/added/weakened: 0/0/0.
T remains exactly entropy_law, entropy_kernel, observation, and hypothetical.

No new Lean theorem was produced. Kernel trust audit: pending, with no new
#print axioms claim; extraction and ELF receipts mark it N/A. The source-boundary
review is `trust-audit-status.md`, not a kernel audit. Budget is 0/100 Lean and
0/2 Kani; IDs 50600–50899 unused, final 50897–50899 reserved. The stop is the
explicit outside-repair blocker, not exhaustion or a checked ROW counterexample.

Next deliverable: lead ruling on the unapplied range-loop proposal; if allowed,
apply only that repair, test the newly reached extraction boundary, re-gate all
three ELFs after the final repair, and accept no R_shipped until its emitted body
and concrete helper links are kernel checked. Combined gates (b)/(c) stay with
the lead. Commit history since entry is in commits-since-entry.txt.
