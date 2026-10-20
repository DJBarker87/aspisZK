# Final frozen-verifier CU bound — 20 October 2026

Target: `fa894d83d2f3ad6df34bc8493881c780621d553e`, branch
`codex/cx-cu-bound4-20261020`; frozen verifier source `b2727acd3`.
Method: `PREREG-CU-UPPER-BOUND-2-20261019.md`, with the admitted-domain
ruling in `LEAD-REVIEW-CU-BOUND-3-20261020.md`: split `[3,10]` only.
Analytical arguments with executable checks; no formal CU theorem is claimed.

## Artifact identity

The freeze's executable table and the actual rebuilt artifact agree:
default verifier `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34`,
1,507,400 bytes; linked verifier `cff391a766c1085e4c1673268c0e6ace53a9e1b3ae9ef406bab5fb978d755486`,
1,563,304 bytes. Pool is `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.

The hash `f11e40b4119578eee1ebef90874f436dc35b1076f6db27baaa92a79c0919538d`
labelled "default verifier ELF" in the lead decision/request actually hashes
`Stage2.llbc`, 7,009,202 bytes. This discrepancy is recorded, not silently
used as an executable identity. The CU analysis targets the executable in
`FREEZE.md`'s executable-pins table. `pins.json` verifies both identities.
All 58 freeze-source hashes match; no verifier source is changed.

## Execution and corpus

Host workspace: `/home/dombarker/project-offloads/codex-cx-cu-bound4-20261020`.
All executable gates run in individual scopes with MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Native Rust uses release mode,
`-j 4`, `RUSTFLAGS='-C link-arg=-Wl,--threads=4'`; SBF direct-lld flags use
`--threads=4`. The line-map build additionally caps host proc-macro linking
through a native `cc` wrapper. Its initial failed linker receipt is retained;
this was thread exhaustion, not memory pressure. No cap was raised.
No Lean was compiled; `#print axioms` is N/A.

The six saved controls reproduce the frozen gate's stage-1 and settlement
CU exactly. The prior bound3 grid and random corpus are remeasured against
the frozen ELF with the exact retained proof/public bytes. Their random
witnesses and OS-generated masks are preserved; no mask is reconstructed
from a public seed. This is a new-ELF replay of the prior random corpus,
not a claim of newly sampled masks. Every replay gets a new receipt.

The optimized component executable verifies bit-reversed query geometry,
including globally distinct 22-query batches with six-slot node counts
`[146,146,128,172,172,150]`, total 914. Four component multiproofs verify,
and four corrupted siblings reject. This does not force Fiat–Shamir queries
in a complete accepted transaction. The source caps cover arbitrary
accepted query sets. The 4,096 statement-point checks also pass.

## Verdict: PASS over the frozen admitted inputs

| Kind | B stage 1 (analytical) | B settlement (analytical) | Stage-1 margin | Settlement margin |
|---|---:|---:|---:|---:|
| Transfer | **1,294,560** | **1,269,370** | **5,440** | 30,630 |
| Withdrawal | **1,293,942** | **1,282,451** | 6,058 | 17,549 |

All bounds are against **1,300,000 CU per transaction**. Split `[3,10]` is
the sole admitted split, as explicitly ruled by the lead; rejected split
`[3,11]` is outside this bound. There is no split-11 coverage requirement
left open under that ruling.

| Kind | Accepted swept runs | Random corpus runs | Swept max stage 1 | Swept max settlement |
|---|---:|---:|---:|---:|
| Transfer | 373 | 300 | 1,203,212 | 1,177,046 |
| Withdrawal | 373 | 300 | 1,201,826 | 1,186,822 |

The 746 accepted measurements cover positions 0 through 1,048,575,
same-page/rollover/genesis history and fresh/prefunded markers. The grid
has 132 runs; eight additional targets cover trailing-bit extremes and
rent/large marker prefunds. The six controls complete the total. All 740
non-control proofs are byte-identical to their original OS-masked corpus
proofs, verified in `corpus-inventory.jsonl`. Plans retain their original
witness seeds; no private signing key, mask seed or proof payload is exported.
Zero swept values exceed their own variant's B.

## Frozen-ELF derivation and the refactored paths

The CFG and arm costs are rebuilt from the frozen linked/deployed ELFs;
`.text` correspondence passes. Executed conditional branches: **9,356
stage 1, 5,706 stage 2, 1,886 Pool**, total **16,948**. Zero unclassified,
zero irreducible functions and zero loop-entry mismatches. The Pool's
69 `call_once` sites are included. Address rules are carried forward only
through equal named/sized functions with equal instructions after masking
layout-dependent call/lddw operands. Twenty of 72 address mappings fail
that check and are not guessed. The analysis regenerates the rebased rules
before each derivation; the preliminary audit's historical-address snapshot
is not used for B.

`harness/frozen_rules.py` supplies new source-cited caps for all three
unrolled batch-tree copies, insertion sort, leaf traversal, folded duplicate
runs, slot padding and binary levels/parents. The six node capacities remain
914 total; batch parent maxima remain 447 and 527. SHA syscall charges are
separate from SBF instruction costs: 127 CU per binary parent. Subtracting
parent hashes leaves constant non-parent SHA-call counts per kind/role.

The loan-scope code is explicitly included. `candidate.rs:239-251,280-321`
fixes query-loop progress: 10 queries in stage 1, 12 in stage 2, one increment
per successful query; an error exits. Moving the accumulator weights and
constructing the relation view does not restart the loop. Geometry visits
10/12 queries and 50/60 denominators (`verifier.rs:134-177`). Batched weights
initialize/finalize 64 entries (`:205-226`); the basis doubles six times,
with inner width at most 32 and a 64-weight accumulation scan (`:278-290`).
`finish_relation` calls fixed rounds and a 64-term final dot (`:292-321`).
The new dot helper at `0xbc530` has its own explicit cap. Field-value and
error arms remain covered by the per-site branch accounting.

`new-path-audit.json` independently checks **1,322 stage-1 and 1,404 stage-2
executed branches**, and source caps for **32/33 executed loops**, in the
refactored candidate, geometry, batched-weights and relation paths. This is
a subset audit; `sites.json` classifies the entire executed program. Exact
per-variant residual rows are in `analysis/sites-per-variant.json`.

### Re-derived nonempty-batch exclusion

The preliminary conservative calculation counted every never-taken arm
and gave stage-1 B 1,339,926 / 1,339,308 and settlement B 1,316,898 /
1,329,979 (transfer / withdrawal). Those results remain in
`analysis/conservative-before-nonempty-exclusion.json` and the original
analysis receipt. They are superseded by the source-cited classification,
not by a verifier change or a changed acceptance threshold.

The frozen compiler unrolls three trees. At `0x29c80`, `0x2ae68`, `0x2c0e8`,
the first-key check is reached only while `d==0`. Both `d` and key position
start at zero; the first leaf increments `d`, which never decreases. Hence
key position is still zero at this check and cannot be >= n, since n is
10 or 12 (`candidate.rs:173-195`). Source mapping and the exact disassembly
in `first-key-disassembly.txt` identify each copy. Every one of the 70
replays executes each first-key check once and takes the impossible arm
zero times. The source argument, rather than those observed counts,
justifies exclusion `F-FIRST-KEY-NONEMPTY`. This is the frozen equivalent
of predecessor `X-BATCH-NONEMPTY`. It prevents falsely charging downstream
loops as additional entries through an empty-first-key path. Other
never-taken arms are still excluded only by cited reasons or counted.

## Residuals and consistency

Transfer stage 1: measured **1,203,212** + ELF residual **86,028** +
query-scan residual **5,320** + parent-SHA residual **0** = **1,294,560**.
The ELF terms are 48,650 loop trips/exits, 22,569 varying-arm residuals,
11,389 never-taken-arm cost, 2,439 loops inside counted arms and 981
loop-control choices. Withdrawal stage 1 is 1,201,826 + 86,796 + 5,320.

The dominating settlement is withdrawal/rollover/prefunded:
**1,186,822** measured + **77,708** nested-verifier residual + **16,778**
Pool residual + **1,143** parent-SHA residual = **1,282,451**.
Largest stage-1 sites include parent traversal `0x2c848` (6,466 CU),
node-count parents `0xbf558` (4,998), query-scan fallback `0x15b2b0`
(4,690), other tree parent loops (4,515 and 4,472), and circle sampling
`0x5ee88` (3,964). Complete decompositions are in `bound.json` and
`analysis/residuals.json`; no site total is substituted for its residual.

All 70 exact-input register replays match stage-1, nested-stage-2 and
settlement CU of the corresponding measurements. Twelve profiling replays
explain all **58 varying verifier phases**; function-level attribution
explains all **40 varying Pool functions** (counted per variant).
Both unexplained lists are empty. The phase map includes the new inlined
query-loop bodies; profiling ELFs are attribution evidence, not release-CU
measurements. Variants and each settlement-history/prefund B are enumerated
in `variants.json`.

The tightest stage-1 B rises by 1,595 CU from bound3: its identical-corpus
measured maximum rises by 1,158 CU and its ELF residual by 437 CU. The
remaining 5,440 CU margin applies to this exact frozen executable only.

## Evidence and limitations

`validation.json` checks the arithmetic, all variants, >=256 random samples
per kind, exact trace parity, every branch classification, phase attribution
and all 828 native execution receipts. The largest native execution peak
RSS is 187,316 KiB; the 70-input CFG audit takes 126.437 s and peaks at
1,112,148 KiB. All executed gates use zero swaps. The sole build failure
is the retained initial line-table host-linker thread exhaustion; its
replacement changes the linker environment and retains the original caps.
The final independent Pool rebuild also reproduces both frozen Pool pins.

The analysis retains the reviewed second-method assumptions: positional
classes are empirical; counted-arm callee costs use observed inclusive
maxima where admitted; fixed-length scans use observed maxima only with
the constant source shape identified. Mutual exclusion requires a cited
source/ELF reason. This is an all-accepted-input analytical CU argument
under those assumptions, with executable coverage and sweep checks; it is
not a Lean proof or a new source/model/backend refinement result.

Cleanup hashes then deletes **1,332** task trace files totaling
**15,403,402,248 bytes**. `trace-inventory.json` records every path, SHA-256,
size and deletion. All task keys, proof/public sidecars, raw CFG JSON and
build caches remain on the host. No key cleanup, deployment or network
transaction was performed. No executable, signing key or proof binary is
committed.

The final package check passes Python/shell syntax, text-only artifact checks,
all 26 per-variant residual-sum identities, all 746 accepted rows and 828
receipts, and the complete trace deletion inventory. There are **1,656 task
signing-key files retained** on the host and zero remaining large task traces.

`git diff --check` reports one trailing-space line in the retained initial
failed-linker `stderr.log`; raw diagnostic bytes are intentionally preserved.
There are no whitespace diagnostics in authored files.
