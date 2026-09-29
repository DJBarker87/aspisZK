# R59: four-accumulator checked dot

Base: `6af7c8384ccea9dce41e16075cd29f77179bd8a0` (pushed R58).
Branch: `research/v8-r59-caller-audit-20260929`.
Unchanged repaired protocol, proof bytes, transcript, sparse G and T163.

## Complete execution result

| Primary verifier | World 0 CU | World 1 CU |
|---|---:|---:|
| R58 control | 1,540,502 | 1,541,957 |
| R59 four-accumulator dot | **1,516,838** | **1,518,195** |
| Saving | 23,664 | 23,762 |

Select R59. Both distinct genuine proofs accept under the diagnostic cap;
corrupted combined finals give checked Custom(6) errors. All honest/corrupt
1M-cap runs exhaust. Resource failure is not rejection. Same driver, proof
hashes, 256 KiB heap and unchanged accounts. **518,195 CU still needs removing**
from the slower fixture. No universal resource bound is established.

## Measured caller evidence

`r59_callers.py` reads the retained R58 trace, checks its exact deployed and
unstripped text and hashes, and attributes arithmetic leaf execution to the
actual preceding call PC. It asserts leaf entries follow call instructions,
no unexpected nested calls occur, and each leaf's totals equal the original
trace report. No verifier replay was needed for this analysis.

The 65 checked-dot invocations accounted for **111,229 exclusive instructions**.
General multiplication accounted for 310,483 instructions in 2,171 calls;
prepared multiplication for 37,272 in 276 calls. Examples of repeated general
call sites include 250 multiplications in semantic basis generation and three
sites with 163 multiplications each in the ordinary terminal. These are caller
symbol/PC facts, not source-line attribution or promises of removable cost.

The checked dot canonicalized every product's four output limbs and then
canonically added it to the running sum. This provided a concrete target
without changing the expensive calculation's mathematical function.

## Exact source rewrite

Only the staged `crates/aspis-core/src/r25_checked_dot.rs` executable helper
changes. The 195 source-pin set stays the same; every other file hash matches
R58, including the public general multiplier, original reference, parsers and
all protocol code. The stager derives a private raw-product function from the
exact retained R56 guarded formula, removing only its four final reducers and
changing its return type to four u64 intermediates. Input canonicality guards,
raw formula, partial intermediate folds and nonnegative offsets remain exact.

The checked dot still rejects unequal lengths, more than 4,096 terms, or any
noncanonical operand limb. Each raw product output receives one Mersenne fold
and is added into one of four u64 sums. The four existing canonical reducers
run once at the end. Empty input still gives canonical zero. No input
validation disappears and no assumption about a caller's validity is added.

This is not the rejected R26 sixteen-channel accumulator: it keeps the R56
per-product reconstruction and stores only four accumulated residues. It also
does not change general `QM31::mul` or its fallback behavior.

For each bounded raw output `x`,

`fold(x) = (x & P) + (x >> 31)`, with `P=2^31-1`.

The fold preserves the residue modulo P and is below 2^34 for every u64 x.
At most 4,096 terms give a sum below 2^46. Every prefix fits u64, so wrapping
accumulation equals natural-number accumulation. Final reduction gives the
same canonical result as repeatedly reducing and adding individual products.

## Compiled/probed boundary

`AspisV8R19/PartialDot.lean` proves eight generic statements: full-u64 fold
bound; folded list-sum bound; accumulator and every-prefix safety; equality
after delayed output reduction; final canonicality; and the third/fourth raw
coordinate bounds complementing R56's first/two-coordinate proofs.

Focused `lake env lean`: **exit 0, 1.72 s, peak RSS 3,257,256 KiB, zero swaps**,
Lean 4.32.0. Eight axioms audits contain only `propext`, `Classical.choice`,
`Quot.sound`. Cached workspace now has 291 successful source-pinned targets;
unchanged targets were reused. No package-wide rebuild, new axiom or `sorry`.
These leaves are not a universal Rust/compiler extraction theorem.

Optimized actual-source host gates pass:

- 265,536 canonical operand pairs, including all 65,536 selected boundary
  combinations, against an independent u128 model and frozen R55 source;
  every pair also checks the one-term changed dot;
- 24 raw-constructor controls retaining checked rejection and the exact old
  general-field fallback outcome;
- 576 complete dot vectors at lengths 0 through 4,096, including maximal limbs,
  against the retained independent dot; 7,272 invalid operands and two length
  errors; 600,192 retained small-dot comparisons;
- both honest host proofs, 3,281 wire controls (3,280 checked rejections), SBF
  stack gate and the complete SVM executions above.

## Exact trace attribution

World-0 tracing reproduces **1,516,838 CU**, verifies byte-identical compiled
text, and executes 1,411,775 instructions. The only exclusive function change
is `r25_checked_dot`: **111,229 → 87,565**, exactly **23,664 fewer instructions**.
Every other exclusive function count remains unchanged. Integer multiplication
count remains 75,246; the improvement comes from reduced surrounding reduction
and summation work, not fewer field products. This is measured execution for
this fixture, not a worst-case theorem.

Stage: `/home/dombarker/project-offloads/aspis-r20-r59-partial-dot-20260929-a`.
ELF: `40917debbbe0328eba8a4eba97820036e80c210a1df284c43a967c3e5864c1ab`.
Exact stage manifest and all changed source, logs, call-PC analysis, Lean
metadata and trace analysis are retained under `evidence/r59-partial-dot`.

## Reproduction and resources

Run `stage_r59_dot.py --control R58_STAGE --output FRESH_STAGE`, then
`run_r59_full.py --stage FRESH_STAGE --mode host`, `sbf`, `svm`, in capped Linux
scopes. Capture the exact unstripped artifact before another build reuses the
cache. The retained full-trace tools check `.text` equality and clean CU.

NUC MemoryHigh/Max: Rust 5G/7G, Lean 3G/5G, runtime/trace 2G/3G, staging and
collection 1G/2G. MemorySwapMax=0, TasksMax=128; overlapping reservation at
most 12 GiB. Release/offline/locked Cargo, jobs=2, cached dependencies and
overflow checks enabled. Compilation was the expensive phase, not debug
arithmetic or elimination. The Solana skill's source, malformed-input, stack
and full-execution checks were used to select the candidate.

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r59_evidence.py
```

No production protocol path, deployment, transaction submission, merge,
wallet/key operation, negative-regression removal or unrelated change.

## Remaining work

CU: remaining measured target gap is 518,195. Inspect the 26-term mixed-width
opening dots and the repeated ordinary/semantic caller products against the
actual emitted code and retained rejected experiments. A multiplication count
alone is not a performance argument. No under-1M prediction is justified yet.

Privacy: universal sampler/field correspondence, including guarded circle
inversion, remains the first source-specific proof obligation. The full
prover/observer chronology, joint posterior coverage, all semantic messages,
shared-oracle seed/commitment hops, retries/publication and explicit justified
losses remain incomplete. Coherent pre-beta extraction remains a separate
soundness obligation. No full privacy or soundness claim is made.
