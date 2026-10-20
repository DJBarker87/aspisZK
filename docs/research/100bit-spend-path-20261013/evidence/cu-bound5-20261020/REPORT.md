# Candidate all-input CU argument — 20 October 2026

**PASS over admitted split `[3,10]`, under the reviewed second-method assumptions.**
Analytical bounds with executable checks; not a formal CU proof or freeze adoption.

| Kind | B stage 1 | B settlement | Stage-1 margin | Settlement margin |
|---|---:|---:|---:|---:|
| Transfer | **1,293,948** | **1,267,581** | **6,052** | 32,419 |
| Withdrawal | **1,293,330** | **1,280,616** | 6,670 | 19,384 |

All margins are against **1,300,000 CU per transaction**. No sweep value
exceeds its own variant's B. Minimum margin is **6,052 CU**, transfer stage 1.

## Target and reproduced pins

Task base `2318acd430b8474de01e6117248442e3ab0b17b9`, branch
`codex/cx-cu-bound5-20261020`. Candidate source binding
`c16e59e77a8ee3249d61838b535a6a44ac918caf`; all **59** source input hashes
match this worktree and the isolated host copy. Production source is untouched.
The frozen verifier and parked candidate are read only; no merge or push.

Fresh optimized SBF builds reproduce:

| Artifact | SHA-256 | Bytes |
|---|---|---:|
| Default verifier | `f9ecbc275b71cf55886351d9445f93e44198d400f7c519573b8f44c9cdb91ae3` | 1,529,128 |
| Linked default | `a769ea0bc90f04faa282632e09b09e06e27867582ec13323624e2585108a076f` | 1,585,032 |
| Devnet verifier | `3f21a42fa6376edf68be160894c4be50db1940e13234a99934127dd49a06f851` | 1,529,128 |
| Pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 605,704 |

All deployed/linked pins, including devnet and Pool linked artifacts, are in
`pins.json`. Default/devnet `.text` matches; replacing only the two ID slots
at 1,492,256 / 1,492,288 reconstructs the complete devnet ELF. The Pool was
independently rebuilt. No deployment or network transaction was performed.

## Method, measurements and targeted coverage

Method: `design/PREREG-CU-UPPER-BOUND-2-20261019.md`, unchanged, with the
admitted-domain ruling in `LEAD-REVIEW-CU-BOUND-3-20261020.md` and the
reviewed bound4 assumptions. The adapter dispatches both `[3,10]` and
`[3,11]` to stage 1 (`programs/r1-cost-probe/src/r1_pool_adapter.rs:1037-1042`),
but `candidate.rs:270-274` rejects a split other than `compact::SPLIT=10`
(`compact.rs:27`). Split 11 is outside the admitted domain.

All six controls reproduce prep5's CU exactly. All **746** corpus replays
accept: **373 per kind**, including **300 retained random witnesses per kind**.
The 740 non-control proof/public pairs are byte-identical to their original
OS-masked corpus; masks were not reconstructed from public seeds and no new
mask randomness is claimed (`corpus-inventory.jsonl`). The 132-run grid,
eight additional targets and six controls accompany the 600 random runs.
Positions span 0 through 1,048,575, with genesis/same-page/rollover histories,
fresh/prefunded markers, trailing-bit extremes and large/rent prefunds.

| Kind | Accepted runs | Measured max stage 1 | Measured max settlement |
|---|---:|---:|---:|
| Transfer | 373 | 1,202,741 | 1,175,273 |
| Withdrawal | 373 | 1,201,354 | 1,185,046 |

These measured maxima are separate from analytical B. `variants.json`
summarizes the **complete corpus** per variant, not just the grid.

Trace selection includes each grid-variant extremum plus predecessor
geometry/duplicate/query-scan targets. Four settlement variants attain their
complete-corpus maxima outside the grid; those exact random-corpus inputs
were added. The resulting **74** register replays match measured stage-1,
nested-stage-2 and settlement CU exactly. The expanded plan resumes completed
labels without rerunning them. Twelve separate `cu-profiling` replays are
attribution evidence, not release-CU measurements.

The optimized Rust component gate checks 4,096 statement-point cases,
globally distinct 22-query bit-reversed geometry with node counts
`[146,146,128,172,172,150]` (total **914**), four valid component multiproofs
and four rejecting sibling mutations. This does not force Fiat–Shamir queries
in an accepted whole transaction. Source caps cover arbitrary accepted sets.

## Candidate ELF classification and source caps

The candidate's deployed/linked CFG, arm costs and inclusive call costs were
freshly derived. Executed conditional branches: **9,446 stage 1, 5,874 stage 2,
1,886 Pool**, total **17,206**. Every executed branch in **every traced
variant** has a classification. Zero unclassified sites, irreducible functions
or loop-entry mismatches. Pool includes all 69 previously problematic closure
sites. Never-taken arms are excluded only by cited accepted-input invariants
or abort paths, otherwise counted at full cost. Arms combine by max only at
an actual CFG choice; other residuals add.

Strict named/sized whole-function matching, with only layout-dependent
call/lddw operands masked, maps **87 of 89** predecessor address sites.
Unmatched addresses are never guessed. Two canonical-scan headers change
with the new indexed wide-field checker. Current ELF headers `0xc3da0` and
`0xc3e48` implement the 22-opening and four-subslot scans
(`candidate.rs:59-71`). Line tables identify the function but emit `?` for
these headers, so direct counter/limit instruction checks supply the mapping:
initializations `0xc3d78` / `0xc3e30`, outer bound `0xc3db0`, inner increment
`0xc40c8`, inner bound `0xc40d0`. The full context is retained in
`canonical-scan-disassembly.txt`; named numeric caps are in `candidate_rules.py`.
This citation enrichment changes **no bound or operational rule**.

The source audit explicitly covers the indexed checks
(`verifier.rs:40-47`, `compact.rs:139-145`), expanded 28-add semantic boundary
(`r1_semantic.rs:82-113`), checkpoint helpers (`verifier.rs:340-376`), grouped
inactive contraction (`weights.rs:25-44,76-77`), factored Libra helper
(`weights.rs:124-152`) and current relation paths. The supplementary
`new-path-audit.json` checks **1,680 / 3,932** branches and **43 / 55** loops
(stage 1 / stage 2) in these and the query/batch/geometry paths. It labels
positional L0 accounting as the reviewed empirical method, not a proved cap.

Query progress is fixed by `candidate.rs:239-251,279-287,295-310` and
`verifier.rs:289-301`: ten queries before the checkpoint, twelve after;
each successful query advances once. Geometry visits 50/60 denominators
(`verifier.rs:156-181`), batched weights have 64 entries
(`verifier.rs:214-234`, `transport.rs:8-9`), and the final dot has 64 terms
(`verifier.rs:313-332`). Borrow moves do not restart work. Binary parents
remain bounded by **447 / 527**; SHA charges are separate at **127 CU per
parent**. Removing parent hashes leaves constant non-parent syscall counts
within each kind/role. The three nonempty-first-key exclusions are reattached
through identical batch-tree instruction bodies and the invariant at
`candidate.rs:174-195`; observations alone do not justify exclusion.

## Residual arithmetic and consistency

Transfer stage 1:
**1,202,741 measured + 85,887 ELF residual + 5,320 query-scan residual
+ 0 parent-SHA residual = 1,293,948**.
The ELF terms are 48,650 loop trips/exits, 22,428 varying-arm residuals,
11,389 never-taken-arm cost, 2,439 loops inside counted arms and 981 loop
control choices. Withdrawal stage 1 is **1,201,354 + 86,656 + 5,320**.

The dominating withdrawal settlement is rollover/prefunded:
**1,185,046 measured + 77,649 nested-verifier residual + 16,778 Pool residual
+ 1,143 parent-SHA residual = 1,280,616**.
Transfer rollover/prefunded uses the complete-corpus maximum:
**1,175,273 + 77,795 + 12,989 + 1,524 = 1,267,581**.
No site total is substituted for its residual.

Largest transfer stage-1 residuals include binary-parent traversal `0x2be28`
(6,466 CU), node-count parents `0xc4a48` (4,998), query-scan fallback
`0x1607a0` (4,690), the other tree parents (4,515 / 4,472), and circle
sampling `0x5e468` (3,964). `analysis/sites-per-variant.json` records every
site, including zero residuals; `sites.json` supplies caps, exclusions,
source references and dominating-variant maximum/baseline costs.

All **58** varying verifier phases and **40** varying Pool functions
(counted per variant) have listed-site attribution; both unexplained lists
are empty. `validation.json` verifies complete per-variant coverage,
all 26 role/variant residual sums, bounds and sweep arithmetic, >=256 random
runs per kind, full-corpus per-variant maxima and exact trace parity.

Compared with bound4, the tightest stage-1 B decreases **612 CU**. This
comparison is descriptive; neither predecessor addresses nor CU totals are
used without candidate derivation. The four additional complete-corpus
extrema also change the residual baseline for their variants.

## Receipts, retention and limits

Host `/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020` uses
copied caches and isolated sources. All **13 completed gate commands** and
**832 native executions** exit zero with zero swaps. Individual receipts
record exact commands, target/source revision, wall time, peak RSS, no-swap
limits and `#print axioms = N/A` (Rust/SBF only). Scopes use 6G high / 8G max /
no swap / TasksMax 64, with reservation snapshots before additional scopes
against the 55 GiB host budget. Native Rust is optimized, offline/locked,
`-j 4`, with `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`; SBF uses direct
`--threads=4` and the native linker wrapper. Tool versions are in `toolchains.txt`.

The 74-input CFG aggregation exits zero in **174.228 seconds**, peak
**1,158,964 KiB** RSS, zero swaps. The largest native execution peaks at
**187,384 KiB**. The bound derivation, canonical-cap enrichment and final
citation checks have separate receipts; the latter two assert unchanged
numeric bounds. No full corpus, ELF trace campaign or build was repeated
unchanged. Rust component checks use release mode. No Lean was compiled.

Cleanup hashes then deletes **1,406** task `.regs` / `.insns` files totaling
**16,272,987,744 bytes**. `trace-inventory.json` records every path, size,
SHA-256 and deletion. **1,664** measurement-task signing keys remain on the
host, along with fixture keys, proof/public sidecars, build caches and raw
CFG/line-map JSON (pinned in `retained-analysis.json`). No key is destroyed
or exported. No binary, LLBC, compiled object or archive is committed.

The second-method assumptions remain explicit: positional classifications
are empirical; counted-arm callee costs may use observed inclusive maxima
where the reviewed method admits them; fixed-length scans use observed
maxima only with constant source shape. A passing argument under these
assumptions is not a universal machine-checked theorem, coherent soundness
closure, privacy closure, source/backend refinement or freeze decision.
The packet's referenced `C3-SKELETON-20261020.md` and
`PRIVACY-FINAL-20261020.md` do not exist in this task base; this independent
CU job does not depend on them or claim their definitions of done.

No requested CU item remains open within the admitted domain and method.
The frozen verifier and parked candidate remain untouched. Adoption and all
non-CU closure decisions remain with the lead.
