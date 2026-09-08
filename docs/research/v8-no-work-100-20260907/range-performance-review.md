# Range-proved arithmetic and sparse fusion: below 1.2M isolated CU

Date: 2026-09-09. Base: `244ad8bf3a4461727b885f5bd54279966e6970a0`.
Research branch only. Main advanced concurrently to
`49410ae48e1c42dd934cf2aef6fa919e7e5eb712`; it and its unrelated result directory were not modified.

## Result

The isolated repaired verifier accepts three **maximum-frontier, 40,282-byte**
proofs at **1,194,675 / 1,194,522 / 1,194,670 CU**, with an actual **1,200,000**
limit. Each has 296 frontier hashes per tree. The profiled binary also accepts
them below the same limit: 1,198,495 / 1,198,342 / 1,198,491 CU.

This closes the isolated measured engineering target, **not complete-transaction
CU parity**. The binary does not authenticate the caller/account context or
settle a pool. The 5,325-CU worst-observed margin is not a universal CU bound.
Matched full transfer/withdrawal and rollover/current-page transactions remain
unmeasured. Global recovery/FS/full-view-ZK obligations remain unchanged.

Ordinary no-search proving now measures **3.65046 / 3.57416 / 3.54872 seconds**,
mean 3.59111, plus 1.41831 seconds shared setup; peak RSS 202,660 KiB
(197.91 MiB), zero swaps. All three regenerated bodies are **byte-identical**
to the existing v2 proofs. These are NUC host measurements, not phone/browser
latencies or total real replay-extraction costs.

## Measured progression

All rows below use the SAME ordinary v2 proof bytes and profiled accounting
until the explicitly quiet final row. No sum of hypothetical microbenchmarks.

| Change, cumulative unless marked control | Seed 1 CU | Seeds 2 / 3 |
|---|---:|---:|
| Previous retained checked structured verifier | 1,892,792 | 1,894,192 / 1,894,334 |
| Range-exact M31 primitives | 1,545,333 | 1,546,825 / 1,546,678 |
| Range-exact CM31 raw products | 1,364,236 | 1,365,749 / 1,365,579 |
| Fixed-arity bounded product channels | 1,342,125 | 1,343,618 / 1,343,468 |
| Sparse right grouped-mask contraction | 1,307,067 | 1,308,584 / 1,308,393 |
| Two-reduction complex multiply | 1,235,786 | 1,237,257 / 1,237,165 |
| Same layout in prepared multiplier | 1,191,810 | 1,193,215 / 1,193,088 |
| Final quiet binary | **1,187,989** | **1,189,395 / 1,189,266** |

The JSON/logs are authoritative for every measurement. Global
`overflow-checks=true` stays enabled. There is NO package overflow override.

Rejected measured controls:

- Returning to the original source query recombination at the dot-kernel stage:
  1,420,694 / 1,422,184 / 1,422,024 CU (worse than 1.342M).
- Branchless M31 add/sub after schoolbook: 1,350,111 / 1,351,152 / 1,351,241 CU
  (worse than 1.236M). Its equivalence theorem is valid; its SBF implementation
  is slower. The patch remains behind an **inactive** cfg for reproducibility.

## Why the retained rewrites are equivalent

### Exact machine arithmetic, not blanket unchecked arithmetic

The research patches apply only to an isolated NUC source copy.
Repository `crates/aspis-core/src/field.rs` is unchanged.

`M31RangeKernels.lean` proves equality of the explicit wrapping operations and
the original integer expressions under canonical-limb invariants. It covers
add/sub/neg, full-u32 multiplication, both folds of the arbitrary-u64 reducer,
the CM31 raw products, fixed four-product updates, and the separate
three-products-plus-four-limbs affine bound. Four products start from zero;
a fifth product or an arbitrary prior accumulator is NOT licensed.

The existing `V5M31RawMulReduction` supplies the inspected mask/shift-to-mod/div,
second-fold cast, canonical-output and residue bridge. It was not replayed
unchanged. The existing `ArithmeticRewrites.four_prefix` is the symbolic
bounded-prefix ingredient. The new results are natural/integer and algebraic
models, **not an Aeneas translation of the patched Rust**.

The two-reduction complex kernel computes, for canonical a,b,c,d,

```text
real = reduce_u64(a*c + p^2 - b*d)
imag = reduce_u64(a*d + b*c).
```

Both fresh channels fit u64, and the real subtraction cannot underflow.
The added p² has zero residue. The imaginary expression equals the Karatsuba
expression by a ring identity. It costs four raw products and two reductions,
versus three products and three reductions plus reconstruction subtractions.
Reusing this in the prepared multiplier is valid because its private
constructor caches [a,b,a+b]; it need not use that third coordinate for this
layout. Other prepared dot routines still use it.

Input provenance: fixed fields use canonical parsing; packed query decoding
rejects every limb equal to p before arithmetic; transcript sampling rejects
noncanonical limbs; public statement/transition decoding is retained; curve
coordinates, constants and closed field operations provide canonical values.
This is a source audit and differential-test boundary, **not a completed
whole-program invariant/acceptance-equivalence theorem**. Public raw M31(u32)
constructors must not be treated as proving canonicality for arbitrary callers.

### New shared public structure

`sparse_grouped.rs` computes a common right-row contribution and nine normal
corrections, five carry corrections and the final missing-overflow correction.
The right contraction drops from 64 generic products to **16**, without
discarding any residual. Its fast-path guard checks both the actual 64 group
indices and the seven public masks; an unmatched layout takes the reference
path. No honest-witness zero is used.

`SparseRight.lean` proves the four frozen-profile identities over any
commutative ring, in arbitrary normal/carry/high-basis values, after clearing
the common denominator 64. The selected bitmask/carry assembly gives those
variables. Host tests compare both the right contraction and all four final
weights against the reference, including zero/one/degenerate coordinates.
These are kernel-checked algebraic identities plus source-shaped differential
tests, not a translated complete-verifier endpoint.

All retained changes preserve v2 transcript bytes, image weights, shifted
ordinary rows, compact boundary reconstruction, query batch and authentication.
No new proof values, salts, nonces or rounds are introduced. The census remains

```text
697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282.
```

Neither arithmetic equivalence nor improved CU supplies missing security bits.

## Expensive accepted schedules, not favourable small proofs

The optional host-only `ASPIS_V8_MAX_FRONTIER_SCAN` mode fixes commitments,
OOD answers, first response/challenge and final256, then scans the existing
last nonce for a maximum frontier. It reconstructs the actual later responses.
No query challenge is forced and no verifier check changes.

With a predeclared 1,000,000-attempt cap per seed, the first maximum-frontier
schedules took 61,024 / 22,062 / 414,938 attempts and
0.26576 / 0.09588 / 1.81429 seconds. All three bodies have exactly 40,282 bytes.
These are three observed scan latencies, not universal mean/tail guarantees.
This scan **increases** authentication cost for stress testing; it is neither
an honest-prover optimisation nor security credit. The existing nonce selection
powers still belong in the FS resource ledger. Sampler errors are continued
within the declared cap; cap exhaustion aborts the fixture.

The new driver tests each honest proof at 1.2M and 1.4M, then honest plus nine
malformed cases at the diagnostic cap. Each final corpus has 36 rows;
all 27 negatives return explicit checked errors with unchanged accounts.
Bad inactive, first-round, final, fixed field, packed leaf, frontier,
noncanonical, truncation and appended inputs are retained. This is not an
exhaustive malicious-input or sampler-tail CU bound.

Maximum-frontier seed-1 profiled attribution includes semantic terminal
302,461 CU, canonical/query recombination 189,274, internal authentication
145,535, leaf hashing 14,614, grouped terminal 44,271, and structured point
terminal 47,359. The full disjoint checkpoint table is in the results JSON.
Hash cost has not been mislabelled as the entire query/relation stage.

## Reproduce and evidence limits

[Results](range-performance-results.json),
[commands, pins and scope](range-performance-evidence.json),
[runner](experiments/run_range_nuc.sh).
The runner refuses a real Git worktree, checks original/patched field hashes,
applies only research patch files in the task-owned source copy, uses capped
offline builds, audits the emitted stack, and retains all checked parsing.

Focused Lean leaves only:

```sh
cd /Users/dominic/ZK/AspisFormal
/usr/bin/time -l lake env lean -M 7000 /ABS/experiments/M31RangeKernels.lean
/usr/bin/time -l lake env lean -M 7000 /ABS/experiments/SparseRight.lean
```

Lean 4.32.0 / mathlib 81a5d257c8e410db227a6665ed08f64fea08e997. Final leaf
runs: 2.35s / 2,857,877,504-byte RSS and 1.75s / 1,363,935,232-byte RSS,
exit 0, zero swaps. Axiom logs contain only standard propext/Classical.choice/
Quot.sound as applicable. One failed local preflight used a nonexistent
`Int.pow_emod` name; its failure log is kept, then the corrected symbolic
lemma was checked. No retained theorem uses sorry or new axioms.

Optimized field controls exercise all 32 source tests plus independent
u128 modular boundary/differential tests. Host structured/dense comparisons
are run on the newly compiled binary; one earlier accidental invocation of
the old binary during compilation was discarded and is not cited as evidence.

NUC: Core Ultra 7 155H, 22 logical CPUs, 63,608 MiB RAM. SBF tools 1.54 /
cargo-build-sbf 2.3.0; host Rust 1.94.1. Heavy builds use 5G high/7G max,
SwapMax=0; proving uses 3G/4G, SwapMax=0. Final SBF build 33.26s,
589,368 KiB peak RSS, exit0, zero swaps. Direct r10-offset audit max 4,096.
The earlier M31-only build warned about an unused V7 function; it was absent
from the emitted ELF. Final build has no such frame warning. Direct-offset
inspection is not a formal proof about every machine pointer.

Quiet ELF SHA256:
`acb18240780f32b209b6e4f2fb10cc7f00aecfa496c0c2514d1a8b9492ea25e4`.
No synthetic witness/owner-secret values are published in the evidence.

## Decision

Retain the range-exact kernels, sparse grouped contraction and two-reduction
generic/prepared complex multiply. Reject the measured branchless and source
query controls. The isolated 1.2M target now has genuine maximum-body evidence;
there is no reason to enlarge the field/domain or spend soundness margin to
address the earlier dense-reference CU failure.

The next decisive experiment is a **research-only matched complete-transaction
harness**, including authenticated public context and atomic settlement, for
all four transaction shapes against selected V7. Measure that delta before
claiming no regression or choosing the next arithmetic optimisation. The present
margin cannot be assumed to absorb settlement. This checkpoint does not assert
all possible optimisations are exhausted or V8 is production ready.
