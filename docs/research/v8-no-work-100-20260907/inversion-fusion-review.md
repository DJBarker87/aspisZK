# Share the inverse, not the larger array

Research continuation of `09a6dd7aa188b31dd96c898e9b3f5ae296514a70`,
2026-09-09. The previous goal turn made measured progress with the
circle-specific norm. This continuation proves/tests two inversion-fusion
layouts, rejects the first, and retains the second in the research build.
Production, main, wire, transcript and all repaired checks remain unchanged.

## Complete-transaction result

| Complete transaction | Previous maximum | Selected split-prefix maximum |
|---|---:|---:|
| Transfer, current page | 1,063,008 | **1,061,150** |
| Transfer, rollover | 1,075,835 | **1,073,971** |
| Withdrawal, current page | 1,081,305 | **1,079,437** |
| Withdrawal, rollover | 1,094,276 | **1,092,468** |

The same twelve maximum-body proofs save **1,800–1,868 CU each**. The actual
TxV1 limit remains 1,200,000, giving 107,532 CU worst-observed headroom.
All 24 maximum-body cases, 24 ordinary-body cases and two post-real-verifier
failing-Token-CPI rollback controls pass with the same outcomes, protected
accounts, proof identities and settlement. Successful matrices use unchanged
Token3.5 SBF; the two rollback controls use the separately specified failing
Token double. Unsupported rollover stale/replay cases are not counted.

The proof body remains **40,282 bytes**. Same-pool selected V7 is still cheaper
by 20,327 / 39,570 / 43,072 / 43,584 CU. These are fixture maxima, not a
universal bound or a V7 no-regression pass.

The retained ELF is 1,009,240 bytes, 1,792 larger than the preceding control:

```text
74e4023c7d2e4e838c10f7a984fd41e8d56571cfed3af281f9063f46dee287f3
```

See [machine-readable results](inversion-fusion-results.json) for all exact
per-proof deltas, program/source hashes, resources and evidence scope.

## Two implementations of the same arithmetic saving

The preceding verifier called M31 batch inversion for 88 second tower norms
and separately for 44 base fold denominators. Each pass builds prefix products,
inverts its final product, then traverses backwards.

The **concatenated-array control** puts all 132 inputs in one Vec, calls the
existing batch routine once, uses the first 88 inverses for QM31 reconstruction
and borrows the last 44 for the fold. It is correct, but **regresses by
370–448 CU** on every maximum-body proof. Its worst is 1,094,713 CU; its ELF
is 1,008,376 bytes. Its 24-case maximum matrix passes, but this loser was not
expanded into ordinary/rollback matrices.

The **selected split-prefix control** keeps the original input/prefix layouts.
If their final products are p and q, it computes

```text
total = inverse(p*q)
norm_seed = total*q
base_seed = total*p
```

These are exactly inverse(p) and inverse(q). The two ordinary backward loops
then reconstruct the original outputs, without the enlarged joined Vec or
tail copy. This is a materially different buffering/control-flow hypothesis,
not an unchanged retry with new seeds or compiler flags.

Both layouts replace one 38-product M31 inversion with three extra batch
products. Counting the actual fixed inverse chain:

```text
old: 3*(88-1) + 3*(44-1) + 2*38 = 466 M31 products
new: 3*(132-1) + 38             = 431 M31 products
net: 35 products saved.
```

That arithmetic model alone did not predict the complete CU result. Allocation,
loop/access patterns, inlining and register/code layout also changed. The two
measurements demonstrate the importance of implementation layout; they do not
provide an instruction-level attribution of the difference to any one cause.

## Formal endpoint and its actual scope

[`JoinedInverse.lean`](experiments/JoinedInverse.lean) proves the prefix and
backward algorithm over a field, not merely a list concatenation identity.
Its recursive `sweep` builds the same accumulated prefixes and unwinds with
the source's updates `output=p*inverse` and `inverse=inverse*x`; the empty
suffix takes the single inverse. `core` initializes with the first element,
matching the source's omission of an unnecessary identity-prefix step.

The useful endpoints are:

- `sweep_correct` / `core_correct`: every recovered element is its inverse
  when the explicitly checked entries are nonzero.
- `checked_correct` / `joined_eq_separate`: the checked concatenation/split
  equals two checked passes, including empty inputs and zero rejection.
- `products_nonzero` / `shared_product_seeds`: the source's two guarded
  lists have nonzero product, and the shared inversion produces exactly the
  seeds required by their unchanged backward passes.

No hypothesis says the proof is honest or assumes a residual is zero.
The zero guard is essential: omitting it would not justify calling the
source's panicking M31 inverse on a zero product.

This is a kernel-checked source-shaped field algorithm, not a complete
Rust/LLVM/SBF translation. Vec prefix indexing, canonical M31 arithmetic,
the fixed inverse chain, memory safety and compiler lowering remain the
source-audit/differential-test boundary. The field and range overlays are
unchanged. No new machine-word accumulator or deferred-reduction bound appears.

The callback's actual length/index obligations are explicit: q points produce
4q tower norms and 2q base denominators. The private helper checks those
lengths and q≤22. Its source-valid calls are nonempty and use the SAME abc and
selected points as the denominator construction. Shape errors for arbitrary
private-helper arguments are not relabelled as a theorem about all malformed
wire inputs.

The selected split layout returns the separate base inverse Vec and keeps
the original `2*i,2*i+1` fold indexing. The rejected concatenated layout
instead used an 88-entry offset at q22, with a separately proved index bound.
No offset from that rejected layout remains in the selected callback path.

## Tests and check preservation

Both optimized controls cover 1,024 chord profiles, with query lengths 1–22,
synthetic zero chords/denominators, 512 arbitrary nonzero 132-element M31
arrays, maximal limbs, and every possible single-zero position. Full QM31
inverses and base fold inverses are compared to the two original calls.
The split test also compares both new layouts directly and checks empty,
singleton and private shape failures.

The unchanged first coordinate-zero checks run before the helper. The
selected `batch_two` rejects empty lists or any zero in either list before
computing its product inverse. No norm or base denominator is treated as
nonzero merely because the honest fixtures usually have that property.
The earlier circle table/constructor proof is reused, not replayed unchanged.

Canonical parsing, authentication, query order, gamma recombination, quotient
numerators, image/ordinary-row relation, rho injection, later responses and
terminal equality are untouched. The only moved work is deterministic field
arithmetic after the same authenticated openings. There are no new challenges,
transcript calls, hints, claims, nonces, padding or public messages.

The body census stays
`697*16+52+24+22*621+2*296*26 = 40,282`.
There was no prover generation or search run, and no new proving-time/RSS
claim. Global recovery, full-view adaptive ZK and resource-bounded FS keep
their previous status; these equalities supply neither security bits nor a
new numerical error term.

## Buffer and execution costs

For the M31 temporary vectors, the previous source requested
352+352+352+176+176 = 1,408 bytes across five Vec payloads, excluding the
unchanged caller's base input vector and CM31/QM31 vectors.
The concatenated version requested three 528-byte payloads = 1,584 bytes,
176 more despite fewer allocations.

The selected split version returns to the previous 1,408-byte requested
payload inventory. Prefix lifetimes and stack metadata differ; an actual
allocator/peak-RSS delta is **not** inferred to be zero from equal payload
sums. Both executed ELFs have direct-r10 accesses ≤4,096 and no new stack
warning. This is not a whole-machine stack proof.

| Focused job | Exit | Wall seconds | Peak RSS KiB | Swaps |
|---|---:|---:|---:|---:|
| Concatenated optimized test/build | 0 | 34.63 | 559,596 | 0 |
| Concatenated SBF build | 0 | 33.94 | 592,496 | 0 |
| Split optimized test/build | 0 | 35.37 | 560,628 | 0 |
| Split SBF build | 0 | 34.11 | 592,212 | 0 |

Compilation dominates. NUC build scopes use High5/Max7GiB/jobs2, SVM scopes
High3/Max4GiB, all SwapMax0. Rust1.94.1, SBF tools1.54/checked optimized
Rust1.89-dev, LiteSVM0.16.0/runtime4.2.1 and Pool/Registry/Token/driver are
pinned as before. The Solana testing workflow kept selection at matching
complete transactions and rollback, not the multiplication count.

Final Lean4.32.0/Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`
leaf: exit0, 4.41s, 2,883,616,768-byte peak RSS, zero swaps. All eleven final
axiom audits use only standard propext/Classical.choice/Quot.sound. No retained
proof uses `sorry` or a new axiom. The initial eight-theorem leaf passed in
6.86s; adding the split seeds caused one focused preflight failure because
`List.prod_ne_zero_iff` was not present in the pinned Mathlib. A short
structural induction replaced that reference. The failed 11.60s log remains
separate from the final successful proof evidence; its error-generated
`sorryAx` entries are not claimed results.

## Reproduction and publication scope

The [auditor](experiments/audit_inversion_fusion.py) replays both literal
callback/kernel patches in memory against the full starting SHA, checks the
measured source hashes and all 74 transaction evidence records, and validates
the final formal/resource logs. The previous circle-norm auditor now pins its
historical kernel source, so adding the new gated methods does not rewrite
old provenance. Its output still reproduces exactly.

The rejected first source is archived as
`experiments/joined_inverse_concat.rs`. To reproduce it, copy that file to
`joined_inverse.rs` in an isolated starting-checkpoint task COPY and apply the
`joined-inverse-*` patches. For the selected version, use the current
`joined_inverse.rs` and `split-inverse-*` patches. Build/test runners check
exact source hashes first. The old-control build was exercised against the
new sources and correctly refused with exit2 before launching a build.

```sh
# From this research directory, using cached Lean:
bash experiments/run_joined_inverse_lean.sh NEW_LOG
# Pinned NUC COPY with the existing overlays:
bash experiments/run_split_inverse_nuc.sh NEW_TEST_LOG
bash experiments/run_complete_build_nuc.sh split-inverse NEW_BUILD_LOG
ASPIS_POOL_ZERO_FAST=1 ASPIS_COMPLETE_MAX_FIXTURES=1 \
  ASPIS_COMPLETE_TX_LIMIT=1200000 ASPIS_TOKEN_CONTROL=legacy35 \
  ASPIS_TOKEN_ELF_DIR=<pinned LiteSVM elf directory> \
  bash experiments/run_complete_matrix_nuc.sh split-inverse NEW_DIRECTORY
# Remove MAX_FIXTURES for ordinary proofs. Do not set Token control for rollback:
ASPIS_V8_SPLIT_INVERSE=1 \
  bash experiments/run_pool_zero_cases_nuc.sh rollback NEW_DIRECTORY
python3 experiments/audit_inversion_fusion.py
```

Keep the driver CLI at1.4M and the actual TxV1 limit at1.2M. No remote
deployment/RPC, production/main change or witness publication occurred.
Concurrent main advanced to `bdf6156d31c18fdd94a63d45d1e4290a9fecb880`
with an unrelated results directory; it was inspected read-only and preserved.
Only scoped research sources and public synthetic logs/JSON are committed.

## Next bounded experiment

The callback already computes `t=2*x²-1` for each query's line coordinate.
The circle-norm helper then recomputes x² for its even term `A+B*x²`.
An exact internal rewrite is
`(A+B/2)+(B/2)*t`: prepare the half coefficient once, reuse the already
derived line coordinate, and avoid 22 repeated base-field products.

First prove that affine substitution and connect the borrowed line-coordinate
slice to the same selected points; an arbitrary supplied t is not acceptable.
Account for half/add preparation, slice/index handling and code layout, then
measure full transactions. Keep the current split-prefix build unless that
complete comparison wins. This continues shared computation across adjacent
kernels without enlarging the wire, static tables or challenge field.
