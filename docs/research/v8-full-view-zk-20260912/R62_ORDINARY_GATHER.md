# R62: source-derived ordinary correction gather

Base `23cf1bd882ccce6f330a4cafb6d39e54c748b984` (R61), research branch
`research/v8-r62-ordinary-gather-20260929`. No protocol, T163, sparse G,
transcript, proof, production path, wallet, deployment or settlement change.

## Complete-execution selection

| Variant | World 0 CU | World 1 CU | Decision |
|---|---:|---:|---|
| R61 control | 1,507,423 | 1,508,805 | Control |
| Existing two-product primitive for tensor entries | 1,538,501 | 1,539,654 | Reject |
| Gather with generic `qm31_dot` | 1,534,586 | 1,536,001 | Reject |
| **Gather with R59 checked dot** | **1,497,377** | **1,498,764** | **Select** |

Selected saving: **10,046 / 10,041 CU**. Both actual 1M-cap runs still
exhaust; the slower fixture remains **498,764 CU over target**. Diagnostic-cap
honest proofs accept, and corrupted final arrays reject with `Custom(6)`
without resource failure. The two genuine proof hashes, driver, 256 KiB heap
and simulated accounts are unchanged. This is verifier-only execution, not
settlement or a universal resource bound.

The pair candidate is not installed in the selected stage. The first gather
candidate accidentally exercised the old generic Karatsuba dot: `qm31_dot`
does **not** dispatch to R59's checked accumulator. Source inspection and its
trace exposed that mismatch. A fresh source variant explicitly calls
`r25_checked_dot`, retaining the generic dot as fallback. The corrected
experiment is not an unchanged rerun. Both slower results are retained.

## Exact source transformation

The old scalar T163 correction scatters 181 products into 19 coordinates:
163 normal contributions and 18 carry contributions. The selected variant
generates each output's ordered `(delta index, high/carry index)` list from
the pinned `SUPPORT` array, then evaluates that same sum with the existing
R59 checked dot. Maximum length is 30; the source inventory audit verifies
all 181 terms and their output coordinates.

The pivot weight is read before overwriting the now-dead tensor-factor
storage. Sixty existing workspace fields become two 30-element dot buffers.
The 531-field workspace requirement, geometry, inactive/pivot correction and
image term remain. No heap allocation or large array return is added.
Input guards, full canonical reductions and generic fallback remain in the
unchanged field primitives. No parser or cryptographic validation is removed.

The independent general four-output ordinary computation stays unchanged.
Only the scalar-path correction is rewritten; it is compared against the
general computation followed by its final contraction.

## Measured attribution

The selected exact-text world-0 trace reproduces clean CU and records
1,392,314 executed instructions. Exclusive changes against R61 are:

| Function | Instruction delta |
|---|---:|
| General QM31 multiply | -25,883 |
| Checked dot | +26,165 |
| New gather | +5,819 |
| Ordinary scalar terminal | -16,147 |
| **Total** | **-10,046** |

General multiply calls fall from 2,171 to 1,990; checked-dot calls rise from
65 to 84. The total integer-multiplication count stays **75,158**. The products
were moved into summed contractions, not deleted. The trace does not justify
attributing the entire saving solely to reductions or to fewer multiplications.
All other exclusive function instruction counts are unchanged.

## Checks and proof boundary

Each candidate passes release-mode source checks and complete executions:

- 256 arbitrary ordinary/image vectors, including zero, one and maximal
  canonical limbs, compared with the unchanged general source computation.
- Both genuine 24-field public input fixtures.
- Retained 12,032 required tensor-coordinate and 8,448 poisoned-unused-cell
  checks. The scalar workspace is also poisoned.
- Pair candidate: 262,144 direct coordinate comparisons.
- Both gather candidates: 4,864 output comparisons against the literal old
  scatter on arbitrary delta/high arrays derived from the input vectors.
- 3,281 full-wire cases per candidate, including 3,280 checked rejections;
  both complete host proofs; SBF compilation without frame warnings.
- Actual 1M and diagnostic-cap SVM executions of honest and corrupted proofs.

`CorrectionGather.lean` adds **three compiled theorems**: ordered scatter with
an arbitrary initial accumulator equals that initial value plus the gathered
sum; the zero-initialized specialization; and application of R59's delayed
residue-reduction theorem to the gathered raw-product list. The first two need
only an additive monoid, not honest-input or challenge assumptions.

Focused `lake env lean` compilation: **exit 0, 1.54s, peak RSS 3,259,980 KiB,
zero swaps**, exact source hash/revision recorded. All three `#print axioms`
reports contain only `propext`. The 295 prior cached targets were reused;
the resulting cache has 296 targets. No package-wide replay, new inverse or
hiding assumption, or concrete large-numeral normalization was introduced.

These theorems concern the list/arithmetic interface. The Rust table generation,
workspace reuse and source execution are audited and tested, **not universally
translated into Lean**. They do not establish full privacy or soundness.

## Reproduction and evidence

Selected NUC stage:
`/home/dombarker/project-offloads/aspis-r20-r62-gather-20260929-b`.
Selected ELF SHA256:
`421016a7194a5a5314f156b6347f47bbe42c472adad29e9761161d276eeb1a4b`.

From the exact R61 stage, use `tools/stage_r62_gather.py --checked-dot` with a
fresh output. Omitting `--checked-dot` reproduces the rejected generic-dot
variant. `tools/stage_r62_ordinary.py` reproduces the rejected pair variant.
Then run `tools/run_r62_full.py --mode host|sbf|svm` in bounded NUC scopes.
All 197 source pins are checked before each gate. Preserve the unstripped
ELF for an exact-text trace before another build.

The selected focused Rust compile took 20.27s (521,204 KiB peak); the host
verifier compile 9.14s (357,272 KiB); source checks 0.01s; wire controls 5.34s;
the timed SBF runner 21.72s (600,116 KiB); each SVM run 0.05s. All timed
commands exited 0 with zero swaps. Exact resources for all three variants
are retained in `evidence/r62-ordinary/receipt.json`.

NUC build scopes: High5/Max7 GiB, release/offline/locked/jobs2. Lean: High3/Max5;
runtime/trace: High2/Max3; analysis/collection: High1/Max2. All use
MemorySwapMax=0 and TasksMax=128; maximum overlapping reservation was 9 GiB.
No cold dependency build, key/fixture regeneration or external transaction.
The Solana development skill kept selection at the complete-execution,
canonical rejection and stack boundary, rather than the host results alone.

Audit locally without a build or replay:

```sh
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r62_evidence.py
```

## Remaining work

The under-1M target remains open. Remaining generic-dot call sites and repeated
semantic/ordinary products need caller-level assessment; the failed pair and
generic-gather candidates must not be relabelled as optimizations. No prediction
that local dot changes can remove the remaining 498,764 CU is justified.

The full privacy goal remains active, not replaced by CU. The first security
proposition is still R60's **actual generated square-loop/guarded inverse
execution refinement**, then word-level norm/equality/try-inverse composition.
Shared-oracle and seed/commitment laws, every observer disclosure, adaptive
transcript simulation, failures/retries/publication and explicit justified
loss bounds remain required. Coherent pre-beta quotient-pair extraction remains
separate. C1 negative regressions, fixed-block hiding and local coverage are
preserved and are not promoted to a full-transcript theorem.
