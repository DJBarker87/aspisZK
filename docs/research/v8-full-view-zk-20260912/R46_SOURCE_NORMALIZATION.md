# R46: descending normalization equals the interpolation section

Base `d98154910d890687de0c031635aadd7dbe9dd94d` (R45).
Branch `research/v8-r46-source-normalization-20260929`.

## Result and scope

**37 new Lean theorems compile with standard axioms only.** The descending
remainder algorithm, modeled with exact field operations and the retained
source carry schedule, computes exactly R44's unique low interpolation
remainder. Its coefficient overwrite and four-slot quotient construction
therefore produce the same normalized section. The R45 balanced-G,
sparse-coin, OOD, image-tail and quotient raw/final boundary is composed
with this algorithmic result.

This closes the mathematical algorithm-versus-choice gap. It is **not an
Aeneas extraction or Rust machine-word refinement**, does not compose every
source opening/residual equation, and does not establish any oracle or seed
distribution. Full-transcript privacy and soundness closure remain open.
No protocol, verifier or production code changed; no new Rust or SBF run.
CU is unchanged at **1,620,236 / 1,621,719**, with both 1M runs exhausted.

## The source calculation being justified

The pinned R43 checker builds the natural-basis coefficients of
`P(X) = product_j (X - t_j)` by repeated `times_x` and scalar subtraction.
It constructs `P, X*P, ..., X^9*P`. Starting with the natural-basis unit
of degree `d`, it visits `top = d, d-1, ..., 22`, captures

```
f = rem[top] * inverse(shifts[top - 22][top])
```

and updates `rem[j] -= f * shifts[top - 22][j]` for `0 <= j <= top`.
It negates the result, overwrites coordinate `d` with one, and places that
vector in B/C/D with the compensating `-alpha^slot` A channel.

The Lean model preserves those bounds, the descending order, and the fact
that `f` is captured before the sequential writes. It does not replace the
algorithm with an unspecified polynomial remainder routine.

| Leaf | Theorems | Result |
|---|---:|---|
| `WideFactorLeading` | 9 | Extends retained support/leading proofs through degree 31; small integer schedules only |
| `SourceFactorEvaluation` | 9 | Source scatter multiplies evaluations by x; root construction and shifts vanish at every supplied root |
| `DescendingRemainder` | 10 | Nonzero pivots, root-evaluation invariant, descending support invariant, unique remainder, normalized equality |
| `NormalizationLoopBridge` | 8 | Forward root fold, successive shifts, bounded sequential writes, reverse traversal and final overwrite/slot construction |
| `SourceNormalizationBoundary` | 1 | Algorithmic quotient inherits the complete retained R45 legal-G boundary |

The leading coefficient is a power of `1/2`, proved symbolically. It is
nonzero in every field of characteristic other than two; there is no new
exceptional-challenge event or generic-rank assumption. Root distinctness
is needed for uniqueness of interpolation, not to make these pivots valid.

The reverse-root representation is explicit: a forward `foldl` of the
source constructor equals the retained recursive factor on the reversed
list. Zero-root prefixing is proved equal to successive `times_x` calls.
No root-order discrepancy is hidden by merely comparing product values.

The last overwrite is justified using the proved zero high tail. Without
that invariant, replacing `unit - remainder` by “negate then write one”
would not be a valid generic transformation. The B/C/D slot restriction
is explicit; the source's two writes are not falsely equated with this
formula for slot zero.

## Source locks and execution evidence

The evidence gate checks against R43's actual stage manifest:

- `r43_universal_witness.rs`:
  `eed56f9206bb40af52234e775e38f6a03f87078b484b14fad2cad17b2cd03b95`.
- `r28_source_helpers.rs`:
  `ea1d0cad89a944b0a6edbf1fdbcc5517ff39ce00e7bb427bb58c698cf646b802`.

The retained source checker already executed four actual query schedules
and 112 normalized columns. It is unchanged and was **not rerun**; these
are historical finite checks, not this milestone's universal proof or a
sampler-law theorem. The new universal result is the exact-field Lean
algorithm, with explicit support bounds and distinct-root premises.

Run:

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r46_evidence.py
```

The gate verifies 18 evidence artifacts, 231 source pins, all unchanged R45
pins, all 227 final cached objects' source hashes and the five successful
target logs. Each log records its exact command, exit, wall time, RSS, swap
and `#print axioms`; metadata records toolchain, source hash and base revision.

- Successful focused leaves: **6.11 seconds** combined wall time.
- Peak target RSS: **2,368,304 KiB**; every successful target exit 0/swap 0.
- Every audit uses only `propext`, `Classical.choice`, `Quot.sound`.
- Cached Lean 4.32.0; serial NUC scopes `MemoryHigh=3G`, `MemoryMax=5G`,
  `MemorySwapMax=0`, `TasksMax=128`. Host preflight: 62 GiB RAM, 46 GiB
  available, no other running build scope. Historical host swap usage is
  not attributed to these no-swap jobs.

The three failed predecessors are retained: whitespace-sensitive notation,
an unnecessarily expanded finite-list membership/sum conversion, and an
ambiguous `unit` name. They were fixed locally without raised limits or a
package-wide replay. Large concrete field recurrences were not normalized.

## First remaining source-specific proposition

For the flattened four-channel quotient, prove that the source circle
evaluator with factors `[y,x,T2(x),T4(x),...]` equals the four natural-line
evaluations at `T2(x)` combined as `A + y*B + x*C + x*y*D`. Compose this
with the actual selected query fibres and the retained chord/division/fold
equations. R44's root/final statements and R45's encoded OOD statement
must become one actual-observation theorem, not remain adjacent models.

Rust field/word and array-loop refinement remains separately recorded;
the generic Field proof is not a claim that all unchecked word values
are canonical. The actual residual point/polynomial equations must then
be bound to the normalized directions and used to derive the new fixed-query
challenge polynomial and its degree. Do not reuse the old 1,105 degree
bound for a different polynomial.

The remaining global gates are unchanged: H1's separate support/coverage,
the Schur right-hand side `b - B A^-1 a`, pre-beta coherent extraction,
joint commitments and seed expansion, accepted-prefix shared-oracle law,
adaptive messages, visible failures/retries/publication and the complete
simulator. No new hiding assumption or independent-challenge law was added.
