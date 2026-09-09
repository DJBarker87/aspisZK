# Shared copy-selector assembly: another measured 39k CU

Research continuation of `0fa310741d483db87e91c3e69aa109a65f88e267`,
2026-09-09. The rewrite changes evaluation of a fixed public functional,
not proof acceptance conditions, transcript framing or production defaults.

## Complete-transaction result

| Complete shape | Previous tag7 maximum | Shared assembly maximum | Same-pool selected V7 maximum |
|---|---:|---:|---:|
| Transfer, current page | 1,149,847 | **1,110,647** | 1,040,823 |
| Transfer, rollover | 1,162,334 | **1,123,176** | 1,034,401 |
| Withdrawal, current page | 1,167,477 | **1,128,318** | 1,036,365 |
| Withdrawal, rollover | 1,180,814 | **1,141,606** | 1,048,884 |

Each row uses three predetermined, archived **40,282-byte** proofs. Comparing
identical proof hashes saves **39,090–39,208 CU**. All successes use the real
1,200,000-CU TxV1 cap, complete account authentication and atomic Pool settlement,
with the explicitly pinned classic SPL Token 3.5 SBF. No diagnostic runtime
budget override is used. The worst observed margin is **58,394 CU**.

These are fixture maxima, not a universal bound over statements, PDA bumps,
challenge samplers and accepted schedules. V7 uses the same Pool, Registry,
runtime and Token binary, with its original release build policy; V8 retains
overflow checks. The stronger no-regression requirement remains unmet by
69,824 / 88,775 / 91,953 / 92,722 CU respectively. See
[exact results](scatter-performance-results.json).

## What was removed, and what was preserved

The source loops over 136 frozen links and scatters 272 endpoints into public
copy weights. Many endpoints use the same high-coordinate selector, flag or
sum of selectors. The new generator reads the actual frozen table and emits a
shared addition plan. It replaces runtime table interpretation, repeated
indexing and repeated sums; it does not omit a constraint.

There are 43 public flag classes: constant one, transfer, withdrawal, twenty
left index bits and twenty right index bits. Thirty weighted selector cells
and forty-three pattern cells are computed. Pattern cells remain unweighted,
including when the corresponding copy weight is zero. In particular this is
**structural sharing, not honest-proof zero elimination**.

The original 544 additive contributions become 59 shared addition nodes,
20 remaining form additions and at most 85 weighted-group combination
additions: **164 additions** before compiler simplification. All 115 weighted
groups and 43 pattern forms remain represented. The source caller constructs
zeroed scratch before filling it; the rewrite does not claim overwrite and
accumulation are equivalent on arbitrary pre-existing scratch.

The first thirty scratch cells used by the alternative tag path are untouched;
the selected tag-dot kernel, copy residual, low selectors, semantic constraints,
masking and relation checks are unchanged. Image/row/query checks and their
causal order remain intact. No parser, denominator test, inverse, proof value,
nonce or transcript message is added or removed.

The fixed body census stays
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes.
The additional 59-QM31 node buffer costs **944 heap bytes**. The verifier ELF
grows from 908,840 to **965,056 bytes** (+56,216); this is code size, not proof
size. The direct-r10 audit reports 4,096 bytes and no new SBF stack warning;
that audit is not a whole-machine stack proof.

## Formal and source correspondence

[generate_copy_scatter.py](experiments/generate_copy_scatter.py) pins the
actual frozen table SHA and checks every generated additive form independently
as an integer coefficient vector. `--check` rejects stale generated output.
It emits straight-line Rust and the following small Lean dependency chain:

| Result | Established scope |
|---|---|
| [CopyScatterNodes](experiments/CopyScatterNodes.lean) | Boolean selection and named specifications of every shared sum |
| [Cells30](experiments/CopyScatterCells30.lean), [Cells55](experiments/CopyScatterCells55.lean), [Cells80](experiments/CopyScatterCells80.lean) | Equality of each generated coordinate to the literal original endpoint-order sum |
| [CopyScatterPlan](experiments/CopyScatterPlan.lean), `all_modified_cells` | Equality of **all 73 modified cells**, for arbitrary selectors and weights over any commutative ring |

Thus correctness is not restricted to Boolean/honest selector assignments or
an honestly zero residual. The instantiated Rust public flags are also tested
against the actual source `link_weight` function. The generated plan is selected
only under `v8_copy_plan`, which requires the selected tensor/tag features.

The [actual-source patch](experiments/copy-scatter.patch) retains the old
assembly for differential tests. Optimized checked Rust passes 3,735 full
103-cell comparisons (basis, arbitrary and all-max canonical selectors;
independent flags), 69,632 public-flag/link comparisons, and the dependent
copy-lane/typed-table tests. These are finite source differentials, not an
exhaustive machine proof. Lean proves the universal algebraic model; it is
**not an Aeneas translation of Rust, parser, compiler or whole verifier**.

All five focused Lean leaves pass without `sorry` or new axioms. The final
theorem uses only `propext`, `Classical.choice`, `Quot.sound`. Individual node
and coordinate proofs use the recorded smaller axiom sets. A preliminary
73-entry vector proof hit definitional recursion depth; the generator now
emits three small tables and combines their proved coordinates. The cap was
not raised. The earlier external-package `-R` invocation fix and both failed
logs are retained.

## Execution and measurement scope

The final build passes 24 maximum-body and 24 ordinary-body cases: twelve
successes per matrix plus malformed-proof, wrong-release, stale-lane and replay
controls. Two further cases fail Token CPI **after the real verifier** and
preserve protected accounts byte-for-byte. Those deliberate CPI-failure
controls use the harness's failure processor, not the classic Token success
binary. Unsupported rollover stale/replay cases are not counted.

NUC Rust/SBF jobs use 5/7-GiB High/Max scopes; SVM uses 3/4 GiB, all with
`MemorySwapMax=0`. The optimized Rust command took 33.03 s / 642,820 KiB peak
RSS, including compilation (test execution 0.04 s). The SBF build took 33.25 s /
589,608 KiB. Both exit zero with zero swaps. Focused cached Lean leaves took
1.83–3.33 s each and at most 2,986,344,448 bytes RSS, zero swaps. Exact commands,
toolchains, source hashes, ELF hashes, leaf/olean provenance, axioms and exits
are in [evidence](scatter-performance-evidence.json) and its linked raw logs.

The winning verifier SHA256 is
`ca69a21b1dcdfab5372396b4a6fc6273d8702e616823593b2319991496f17a66`.
Runtime is LiteSVM 0.16.0 / Solana runtime 4.2.1 / SBF tools v1.54.
The Pool/Registry hashes match the previous comparison. No new prover timing
or RSS measurement is claimed: the proofs are byte-identical archived inputs.
No witness or secret-bearing binaries are committed.

## Reproduce

`experiments/` below means this research directory's experiments path. On the
documented task-owned NUC copy after the tag7 checkpoint overlays:

```sh
bash experiments/run_copy_scatter_nuc.sh prepare NEW_PREPARE.log
bash experiments/run_copy_scatter_nuc.sh test NEW_TEST.log
bash experiments/run_complete_build_nuc.sh scatter NEW_BUILD.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh scatter NEW_DIRECTORY
ASPIS_V8_SCATTER=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
```

Remove only `ASPIS_COMPLETE_MAX_FIXTURES` for the ordinary-body matrix. The
preparer fails closed on an unexpected source hash; do not reset a worktree
to satisfy it. Locally, run each named Lean leaf in dependency order with
`run_copy_scatter_lean.sh LEAF ABSOLUTE_NEW_LOG`. For read-only evidence checks:

```sh
python3 experiments/generate_copy_scatter.py --check
python3 experiments/audit_scatter_performance.py
python3 experiments/audit_scatter_evidence.py
```

## Decision and bounded next gate

Retain this rewrite: it removes repeated public computation with a universal
algebraic certificate and a substantial same-proof full-transaction saving.
It spends no soundness margin and changes no transcript, but does not close
the inherited global recovery, full-view ZK, FS or universal-CU obligations.
Grinding credit remains zero; production remains unchanged.

The next concrete arithmetic candidate is the frozen tag structure
`tag_i=(67<<24)+i`, for `i=0..135`. For canonical limbs let `S=sum(a_i)` and
`D=sum(i*a_i)`. Since `2^31=1 mod p`, the raw replacement is

```
67 * (((S mod 128) << 24) + floor(S/128)) + D.
```

It could reduce all thirty tag coordinates once rather than in fifty-two
seven-product chunks. A conservative 272-term bound is
79,304,104,796,113, below `2^64`. Twenty-four of the thirty unweighted tag
selector sums already match an input or node in the new shared plan. These
are exact inventory/arithmetic observations only, **not yet a proved or
measured kernel**. The next experiment is to prove the congruence and every
intermediate range, integrate a source-shaped control, and measure it against
this scatter build. Reject it if code generation outweighs the reduction
saving; do not claim operations saved are CU saved.
