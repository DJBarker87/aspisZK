# Tag-prefix splitting: range proof turns a regression into a saving

Research continuation of `4d5f3063412349f5cba9b0b6b7d166d24814eb91`,
2026-09-09. This is a byte/transcript-preserving evaluator change to the
repaired research verifier. Production source/defaults and main are unchanged.

## Measured decision

Retain the bounded tag-prefix kernel. Reject the ordinary checked-accumulator
version as a performance control: despite using fewer field reductions it
**regresses by 14,143–14,162 CU** on identical complete maximum-body proofs.
Removing only the specifically proved redundant overflow checks changes that
to a **3,754–3,773 CU saving** over the preceding shared-copy build.

| Complete transaction | Shared-copy build | Bounded tag-prefix build, maximum observed |
|---|---:|---:|
| Transfer, current page | 1,110,647 | **1,106,879** |
| Transfer, rollover | 1,123,176 | **1,119,414** |
| Withdrawal, current page | 1,128,318 | **1,124,560** |
| Withdrawal, rollover | 1,141,606 | **1,137,838** |

All twelve predetermined maximum-body successes execute with the actual
**1,200,000-CU TxV1 cap**, matching Pool/Registry/runtime/classic SPL Token 3.5
SBF and archived proof hashes. The observed worst margin is **62,162 CU**.
The maximum body remains exactly **40,282 bytes**; serialized transaction
sizes are distinct and remain recorded in the result JSON.

The total improvement since the earlier 1,180,814-CU tag7 checkpoint is 42,976 CU
at the maximum-observed rollover withdrawal. These are measured fixture maxima,
not universal CU bounds. Same-pool selected V7 remains cheaper by 66,056 /
85,013 / 88,195 / 88,954 CU across the four shapes. Its original release policy
is retained; global V8 overflow checks remain enabled. See the individual
same-proof comparisons in [tag-split-results.json](tag-split-results.json).

## Exact rewrite

The source table has 136 tags, all exactly `tag_i=(67<<24)+i`, `i=0..135`.
A compile-time assertion checks every actual tag. For any coordinate and any
one of its four canonical M31 limbs, write

```
S = sum a_i
D = sum i*a_i
original = (67<<24)*S + D
rotated(S) = (S mod 128)*2^24 + floor(S/128).
```

Because `128*2^24 = p+1`, the **integer equality** is
`S*2^24 = rotated(S) + floor(S/128)*p`. Therefore reducing
`67*rotated(S)+D` once returns the same field value as the original tagged
dot product. This applies to arbitrary canonical selector limbs, including
all-max values, not just actual honest multilinear selectors.

There are thirty actual coordinates. The previous seven-tag kernel uses
fifty-two chunks / 208 limb reductions; the replacement uses thirty complete
coordinates / **120 reductions**, while preserving all 272 tag terms. It also
adds a raw `S` accumulation, which must be charged. The first SBF control shows
why reduction counts alone are not a CU estimate.

The new shared-selector plan is reused unchanged, but **this version does not
yet reuse its existing sums for S**. The earlier observation that 24 of the
30 tag sums match that plan is a future fusion opportunity, not an implemented
saving in these numbers.

## Range and equivalence proof

[CopyTagSplit.lean](experiments/CopyTagSplit.lean) proves the literal list split,
integer rotation equality, final modular equality, accumulator bounds and all
prefix bounds. The deliberately conservative limit of 272 terms gives:

```
S <= 584,115,551,712
D <= 78,855,599,481,120
67*rotated(S)+D <= 79,304,104,796,113 < 2^64.
```

Each raw product is also bounded. Since all terms are nonnegative, the
intermediate rotation addition and scaling are bounded by the final expression.
The leaf proves that wrapping products, partial sums and the final sum equal
the corresponding ordinary natural-number operations at these ranges.
The tag-offset subtraction is safe by the frozen-table assertion. Indexing,
canonical parsing and other overflow checks have not been disabled.

[copy-tag-split.patch](experiments/copy-tag-split.patch) is the first control;
[copy-tag-bounded.patch](experiments/copy-tag-bounded.patch) adds inlined
wrapping operations only inside these bounded raw accumulators, under
`v8_copy_tag_bounded`. No global `overflow-checks=no` option is introduced.
The real function is compared to the source literal modular dot product on
15,360 coordinate cases, including canonical extremes, and the complete
selected copy-lane module's eleven tests pass under both configurations.

The formal result is kernel-checked natural-number/algebraic/range equivalence.
It is not a translated Rust/LLVM/SBF proof. In particular, the concrete
machine interpretation of masks/shifts and existing canonical field operations
is supported by actual-source differential tests and the inherited field
interfaces, not a newly claimed Aeneas endpoint.

The final focused Lean replay exits zero in 11.67 s with 2,841,591,808-byte peak
RSS and zero swaps. Only standard `propext`, `Classical.choice`, `Quot.sound`
appear in the axiom audit; there is no `sorry` or new axiom. The initial
algebra/range leaf also passed (12.94 s / 2,831,204,352 bytes / zero swaps).
The subsequent replay was required by adding the wrapping-interface lemmas.
Both use the pinned **4.32.0** Mathlib workspace, not the research directory's
different default Lean version. Cache revision and Tactic olean hash are pinned
in [artifacts](tag-split-artifacts.json).

## Complete tests, costs and boundaries

The slower control has 24 maximum-body cases. The selected bounded build has
24 maximum-body and 24 ordinary-body cases, including wrong release, malformed
proof, stale lane and replay controls. It also passes two post-real-verifier
Token-CPI-failure rollback tests, which retain the dedicated failure processor.
Successes use the pinned classic Token SBF. Protected accounts remain unchanged
on the tested failures. Unsupported rollover stale/replay cases are not counted.

The initial and bounded Rust commands take 33.13 / 33.06 s, with 642,516 /
643,472 KiB peak RSS. SBF builds take 33.42 / 33.32 s with 589,104 / 589,156 KiB.
All exit zero with zero swaps; compilation dominates the Rust command, whose
test execution is approximately 0.05 s. Build scopes are High5/Max7 GiB; SVM
scopes High3/Max4 GiB; all set `MemorySwapMax=0`. No broad Lean replay occurs.

The selected verifier is **964,584 bytes**, 472 bytes smaller than the scatter
ELF; no heap allocation is added by this change. Both controls pass the direct
r10-offset audit at 4,096 bytes with no new SBF stack warning. This is not a
whole-machine stack proof. Proof bytes, proof-account lifecycle and transcript
are unchanged. No new prover-time/RSS measurement or end-to-end proving claim
is made; exactly the archived proofs are reused.

Selected ELF SHA256:
`0ddb88cbfc1c10b6510028048b1b124e426b9b7fb295ca14ba8400e1cb2cafd9`.
Source/ELF pins, raw logs, resource metrics, proof hashes and rejection outcomes
are linked from [results](tag-split-results.json) and
[artifacts](tag-split-artifacts.json). The initial patch application failed
closed due to insufficient context; adding unchanged trailing context fixed it
before any source modification or compilation. No check was bypassed.

## Reproduce / next gate

On the task-owned NUC copy after the scatter overlay, with `experiments/`
abbreviating this research directory's experiment path:

```sh
bash experiments/run_copy_tag_split_nuc.sh prepare NEW_PREPARE.log
bash experiments/run_copy_tag_split_nuc.sh test NEW_TEST.log
bash experiments/run_complete_build_nuc.sh tag-split NEW_BUILD.log
bash experiments/run_copy_tag_split_nuc.sh prepare-bounded NEW_BOUND_PREPARE.log
bash experiments/run_copy_tag_split_nuc.sh test-bounded NEW_BOUND_TEST.log
bash experiments/run_complete_build_nuc.sh tag-bounded NEW_BOUND_BUILD.log
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh tag-bounded NEW_DIRECTORY
ASPIS_V8_TAG_BOUNDED=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_ROLLBACK_DIRECTORY
```

Run the maximum matrix at `tag-split` as well for the rejected-control
comparison. Remove only `ASPIS_COMPLETE_MAX_FIXTURES` for the ordinary matrix.
Locally, `run_copy_tag_split_lean.sh ABSOLUTE_NEW_LOG` runs the single leaf;
`audit_tag_split.py` rechecks the archived results without replaying tests.

The next bounded experiment is to reuse the 24 already-available **modular**
selector sums, with a proved reduced-S interface, and generate the small-offset
dot products alongside the shared selector assembly. Compare the entire
pipeline against this bounded kernel; do not count savings from a microkernel
that duplicates preparation or increases another stage. This has not been
implemented or measured here.

The image gate, shifted rows and degree-q query batch remain untouched. No
positive grinding credit is introduced. These performance rewrites do not
resolve global recovery, full-view simulation or resource-bounded FS, nor the
stronger matched-V7 no-regression requirement. They do establish another
measured saving from an exact, range-justified specialisation.
