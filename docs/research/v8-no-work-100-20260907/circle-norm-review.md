# Circle-only chord norm: prove the input invariant, then remove its redundant term

Research continuation of `b082d32c3deec5a4b48f4ceba41e44d167b2278b`,
2026-09-09. **Retain this control over the six-coefficient chord-norm winner.**
It is not either of the rejected gamma-head layouts. Production, main, field,
domain, wire, transcript and all repaired checks remain unchanged.

## Measured decision

| Complete transaction | Six-coefficient maximum | Circle-only maximum |
|---|---:|---:|
| Transfer, current page | 1,063,909 | **1,063,008** |
| Transfer, rollover | 1,076,729 | **1,075,835** |
| Withdrawal, current page | 1,082,205 | **1,081,305** |
| Withdrawal, rollover | 1,095,156 | **1,094,276** |

The same twelve maximum-body proofs save **861–911 CU each**. All24
maximum-body cases and24 ordinary-body cases pass, with unchanged expected
acceptance/rejection, proof identity, protected accounts and settlement.
Two additional withdrawal rollback controls pass after the real V8 verifier,
using the same deliberately failing Token-CPI double as the previous control.
The successful matrices use pinned Token3.5 **SBF**, not that double or a
native Token builtin. Unsupported rollover stale/replay cases are not counted.

The worst measured case has **105,724 CU headroom** below the actual1,200,000
TxV1 cap. The maximum body is still **40,282 bytes**. The selected ELF is
**1,007,448 bytes**,280 bytes smaller, SHA256:

```text
ad5b5d30dd0f8c5d1f2f2262840517f3c5e2f3a0160fd4c8bb23d4d5f99c0dba
```

Same-pool selected V7 is still cheaper by22,185 /41,434 /44,940 /45,392 CU.
These remain fixture maxima, not a universal CU bound or no-regression pass.
[Machine-readable results](circle-norm-results.json) preserve the comparisons
and evidence scope without filling missing global security terms with numbers.

## The invariant is constructed, not assumed about public point inputs

The winning six-coefficient kernel was correct for arbitrary M31 x/y. Its even
term was `N(a)+N(b)*x²+N(c)*y²`, with `N(v)=v0²-(2+i)*v1²`.
On the circle this equals

```text
(N(a)+N(c)) + (N(b)-N(c))*x².
```

Dropping y² for arbitrary points is false. The new Rust
[`Selected` wrapper](experiments/circle_norm.rs) has private fields; its only
non-test constructor calls the actual
`selected_circle_fiber_points_shared(20,queries)`. It exposes only an
immutable point slice. The callback derives its denominators from that slice
and the same `p.abc`, then calls the wrapper's inverse method. No prover hint,
unchecked unit flag, arbitrary point constructor or late point mutation is
introduced.

The pinned log20 constructor selects one entry from each of three64-entry
windows, then performs its two optional complex/group additions. We extracted
the exact192 public table entries from the NUC's generated source. The
[snapshot](experiments/circle-window-points.json) is checked against the actual
compiled Rust arrays, not merely a reimplementation of the generator.
All entries are canonical. The inspected generator and point-source hashes
match locally and on the NUC:

```text
build.rs      7905b8c2a92c72a79a8a6c785a91ce162fb338569a02867f671d1910e21b6e0d
circle_fri.rs 77625499c80b30fe9de1e79daaf35dc964bf0cb675a65ced69592d3d421c856b
```

The generated full `circle_tables.rs` read from the NUC has SHA256
`9db9976bb1fc1d795026bf647ccecb85ba1b9522bad71bbc8d0346271806a4de`.
Only the three relevant arrays are retained, not the large generated file.

## What the formal endpoint establishes

[`CircleNorm.lean`](experiments/CircleNorm.lean) proves circle-addition closure
symbolically, the optional-window construction, preservation under a ring
embedding, and the four ordered norm outputs. The previous `ChordNorm`
source/olean is reused with its recorded hash; it is not rebuilt unchanged.

[`CircleNormTables.lean`](experiments/CircleNormTables.lean) kernel-checks
each concrete table entry as a `UnitPoint (ZMod 2147483647)`. Each certificate
reduces only two products; no full262,144-point recurrence is normalized.
Its source-shaped `selected` function performs the same two conditional
group additions. `selected_norms` therefore supplies all four norm identities
for **every choice of the three six-bit windows**, after embedding into the
coefficient ring, without assuming circle membership as an external premise.

The input-invariant proof is materially stronger than the earlier conditional
`circle_even` lemma: the relevant table values now carry checked certificates,
and closure transports them through the actual addition expression. It does
not prove the entire Rust/LLVM/SBF execution. Exact Rust integer field kernels,
bit reversal/window indexing, the private caller's shared arguments and
compiler lowering remain source-audited/differential-tested boundaries.
The prior range-proved field overlay is unchanged. No extra machine-word
accumulator or deferred-reduction range is introduced.

An optimized test checks all262,144 legal log20 indices, table-snapshot
identity, invalid indices,1,024 arbitrary QM31 chord profiles, all four slots,
near-maximal limbs, deliberately zero denominators, empty/shape failures,
four legal unit points with a zero coordinate, and the off-circle falsifier.
Each computed norm and full inverse is compared against both the retained
six-coefficient and direct tower implementations; nonzero inverses multiply
back to one. These are finite implementation checks, not an experimentally
estimated soundness probability.

The first point-coordinate zero guard, empty/zero denominator guards, second
norm's zero check, M31 batch inverse and final conjugate reconstruction remain
in place. Queries, gamma, canonical leaf decoding, authentication, image/row
relations, rho injection, response order and terminal check are untouched.
Thus this is a byte/transcript-preserving arithmetic specialization, not a
new sampler or a challenge-distribution change.

## Complete cost, not only the removed multiplication

Coefficient preparation still performs6 CM31 squares and6 CM31 products.
It adds two CM31 add/sub operations to prepare the new even coefficients.
Across22 fibres, CM31/base scalings decrease110→88 and point products
decrease66→44. With the selected two-product square and four-product
schoolbook CM31 product, this first-norm subcomputation decreases
**322→256 base products**, including preparation. Other additions, reductions,
accesses and layout also change; the measured CU saving is not assigned only
to those66 omitted products.

Coefficient payload decreases48→40 bytes. The88-entry CM31 norm vector remains
704 bytes, with unchanged inverse output lengths. The wrapper adds no new
Vec or allocation: it owns the point vector previously owned by the callback.
Allocator/whole-frame peak delta was not measured separately. Executed ELF
direct-r10 offsets are at most4,096, with no new stack warning; this is not a
whole-machine stack proof.

No prover execution, search, proving-time/RSS or network measurement was
repeated. The unchanged body census is
`697*16+52+24+22*621+2*296*26 = 40,282`.
No transmitted scalar, nonce, padding, proof round or transcript call is added.
Global recovery, full-view adaptive ZK and resource-bounded FS retain their
previous status; these equalities add no security bits or new numerical error
terms.

## Evidence and resources

| Focused target | Exit | Wall seconds | Peak RSS | Swaps |
|---|---:|---:|---:|---:|
| Optimized source test/build | 0 | 34.44 | 559,356 KiB | 0 |
| Complete SBF build | 0 | 34.05 | 591,652 KiB | 0 |
| CircleNorm leaf | 0 | 1.60 | 2,876,358,656 bytes | 0 |
| CircleNormTables leaf | 0 | 2.43 | 2,900,525,056 bytes | 0 |

The twelve final axiom audits use only standard propext/Quot.sound; the
embedding lemma needs none. No retained proof has `sorry` or new axioms.
Lean4.32.0, pinned Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`,
source/olean hashes and resource logs are recorded. The generated-file
`--check` passes.

Two local preflight corrections remain explicit. The first successful
CircleNorm invocation lost its file log because a relative log path was
resolved after changing directory; the wrapper exited1. The runner now
canonicalizes the log path, and the focused replay above supplies the missing
evidence. The first table leaf failed in2.02s because the opaque `unit`
predicate had no inferred Decidable instance; the generator now unfolds only
that small predicate before each bounded `decide`. Its failed log is retained,
not presented as a successful theorem.

The first rollback command incorrectly combined the explicit successful Token
SBF control environment with the failing-CPI-double scenario. The driver
refused that mixture **before executing the transaction** (exit1). Its failed
v1 log is retained. The correctly separated v2 run supplies the two rollback
results. No malformed proof was repaired or favourable proof seed selected.

NUC Rust1.94.1, SBF tools1.54/checked optimized Rust1.89-dev,
LiteSVM0.16.0/runtime4.2.1, Pool/Registry/Token/driver and previous proof fixtures
are unchanged. Compilation dominates. Builds use High5/Max7GiB/jobs2; SVM
uses High3/Max4GiB; every NUC scope has SwapMax0. Main advanced concurrently to
`05761d0cdc778fc7ac349f2be481d89959980960` with an unrelated results directory;
it was inspected read-only and preserved.

The auditor replays the literal callback patch in memory against the full
starting revision, verifies all50 successful evidence cases, table/source/ELF
identity, resource limits and final axiom logs. The preceding chord-norm and
gamma-one auditors still pass without heavy replays.

```sh
# From this research directory:
bash experiments/run_circle_norm_lean.sh CircleNorm NEW_LOG
python3 experiments/generate_circle_norm_tables.py --check
bash experiments/run_circle_norm_lean.sh CircleNormTables NEW_LOG
# Pinned task-owned NUC COPY with the existing measured overlays:
bash experiments/run_circle_norm_nuc.sh NEW_TEST_LOG
bash experiments/run_complete_build_nuc.sh circle-norm NEW_BUILD_LOG
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh circle-norm NEW_DIRECTORY
# Remove MAX_FIXTURES for ordinary proofs; DO NOT set the Token control here:
ASPIS_V8_CIRCLE_NORM=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_DIRECTORY
python3 experiments/audit_circle_norm.py
```

Keep the driver's1.4M CLI setting together with the actual1.2M TxV1 cap.
Only public synthetic JSON/log evidence is copied locally, not witnesses,
proof bodies or ELFs.

## Next bounded optimisation

The query stage still calls M31 batch inversion twice: once for88 second
tower norms and again for44 base fold denominators. A single132-element pass
would remove one M31 inversion while adding three prefix/backward products
relative to the two separate passes. It may also change buffering/code layout.
No prior closed control for this exact fusion was found in the research
inventory; it is distinct from the earlier generic-QM31 batch experiment.

Next prove the concatenation/split and zero-rejection interfaces, preserve
the exact norm/base-index provenance, then measure the combined verifier.
Retain only a same-proof complete-transaction improvement. Do not infer
a CU saving from the saved inversion alone or remove either denominator check.
