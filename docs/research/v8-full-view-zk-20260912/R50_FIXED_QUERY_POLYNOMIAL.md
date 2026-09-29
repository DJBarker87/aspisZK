# R50: fixed-query polynomial and actual-chord gate

Base `559e73c6648f42241e998c4e9f3221082da1594a` (R49).
Branch `research/v8-r50-fixed-query-polynomial-20260929`.

## Result

**38 new Lean theorems compile with standard axioms only.** For every
distinct 22-root tuple over exact QM31, the new full-support residual
determinant is a **nonzero polynomial of total degree at most 819** in the
remaining challenge coordinates. Its evaluation equals the source-shaped
normalized correction matrix. The actual rational-chord determinant is
that evaluation times the thirteenth power of the exact chord scale.

This closes the algebraic target identified in R42, using the normalized
section and source bridges developed since then. It does **not** establish
the source shared-oracle joint law or an adaptive privacy-loss bound.
No production/verifier/protocol change; no new Rust/SBF run. Retained CU
is **1,620,236 / 1,621,719**, and both 1M-cap runs still exhaust.

## Polynomial and source identity

Fix an arbitrary distinct tuple `t` of 22 roots. For each of the thirteen
selected columns, take the normalized scalar section from R44/R46 as
constant coefficients. Multiply it by the exact slot factor

```
[slot = selectedSlot] - alpha^selectedSlot * [slot = 0].
```

The source-normalized column equals this expression, including the
degree-31 D direction. The model retains every code output below 131 and
every quotient input below 128. Its point functionals use the actual
statement-point construction proved in R49. Its ordinary/G functionals
include the inactive/pivot cancellation and the sparse-G boundary at 128.
All seven relation coefficients use the retained reversed-slot kernel.

Only fourteen challenge coordinates vary:

```
0..9: semantic z     10: kappa     11: alpha     12,13: u,v
normalized chord: (1+u*v, u*v-1, -(u+v))
```

The polynomial uses the retained `Fin 36` degree interface for reuse;
coordinates 14 through 35 are unused. Their irrelevance is proved, and
they are **not** supplied with query roots or counted as fresh challenges.
The root tuple is a fixed parameter of the polynomial family.

Ring-homomorphism proofs identify polynomial evaluation with the field
matrix. The generic source bridge is valid for arbitrary semantic points,
kappa, alpha, image challenge and previous G coefficient state. The 270
nonconstant G coefficients drop out of this low functional by the proved
scatter/support argument, not by changing their generation.

Nonvanishing uses R49's exact-QM31 specialization with `kappa=5`,
`alpha=7`, `u=2`, `v=3` and the retained ten-coordinate `z`. It reuses the
certified inverse. This specialization is an algebraic witness, **not** an
accepted OOD prefix or a claim about the sampler's support after conditioning.

## New degree accounting

| Component | Proved total-degree bound |
|---|---:|
| Full transported point code weight | 55 |
| Normalized chord entry | 2 |
| Full point functional weight | 57 |
| Sparse-G boundary weight | 2 |
| Ordinary or G relation weight | 60 |
| Fixed-root normalized quotient column | 3 |
| Any residual matrix entry | 63 |
| Thirteen-by-thirteen determinant | **819** |

The determinant proof uses `13*63` symbolically; no determinant or huge
recurrence is expanded. The old 1,105 bound is neither reused nor renamed.
The new bound concerns the fixed-root family and includes its G term.

## Transfer to actual chord coordinates

Every full-support point and relation entry is linear in the chord triple,
including G. Scaling that triple by `s` multiplies the determinant by
`s^13`. With the retained rational circle parameterization,

```
det(actual source-shaped matrix)
  = chordScale(u,v)^13 * eval(challenges, fixed-query polynomial).
```

Provided `2 != 0`, `1+u^2 != 0`, `1+v^2 != 0` and `v != u`, the scale is
nonzero. Thus source-matrix nonsingularity is equivalent to a nonzero
polynomial evaluation. These domain conditions remain explicit; this
theorem does not identify the actual source sampler with a uniform law.
The source equality is exact-field semantics, not compiled Rust extraction.

## Executed proof evidence

| Leaf | New theorems |
|---|---:|
| `FixedQueryModel` | 5 |
| `FixedQuerySource` | 6 |
| `FixedQueryPolynomial` | 4 |
| `FixedQueryDegree` | 9 |
| `FixedQueryNonzero` | 4 |
| `FixedQueryChordScale` | 8 |
| `FixedQuerySourceGate` | 2 |

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r50_evidence.py
```

Gate: **27 artifacts**, **260 pins**, **257** successful cached objects,
and unchanged R49 source pins. New leaves total **8.65 s** wall time;
peak RSS **2,490,908 KiB**. Every successful target has exit 0 and swap 0;
all 38 audits use only `propext`, `Classical.choice`, `Quot.sound`.

Serial cached NUC Lean 4.32.0 scopes: `MemoryHigh=3G`, `MemoryMax=5G`,
`MemorySwapMax=0`, `TasksMax=128`. Exact target commands, source/base hashes,
wall time, RSS, swap and axiom output are recorded. Failed rewrite, syntax
and instance-plumbing attempts remain in evidence. An early dependent
preflight retried the still-failed prerequisite before its repair; no
package-wide regression or resource-limit increase was used. A looping
`simp` was replaced with explicit case-split/map rewrites.

## First remaining source proposition

Prove a joint-law refinement for the **actual causal transcript experiment**
which permits applying this polynomial family after the source's later
query-root tuple is chosen. A theorem for each fixed tuple does not by
itself make the earlier challenges uniform conditional on that later tuple.
Do not silently condition on acceptance/publication or let an adaptive root
choice masquerade as an independent parameter.

The refinement must account for fresh or previously read squeeze/advance
addresses in the complete shared-oracle trace, canonical QM31 rejection,
bounded nonzero/OOD sampling, the ordered 22-of-262144 query sampler with
cap 64, its extra completion-detection block, and all observable failures.
Both channel coefficients precede beta; alpha follows the first relation
message, and Final256 precedes query indices. Prior adversarial oracle
queries, nonce search, retries and publication selection require explicit
first-hit/collision and stopping/conditioning losses.

No number such as `819/|QM31|` is a proved source privacy bound here.
R42's ideal finite-sampler uniformity and generic freshness lemmas remain
reusable, but their source premises must be discharged rather than assumed.

After that, full joint H1/G and semantic coverage, the Schur target
`b - B A^-1 a`, coherent pre-beta extraction, seed/commitment hops, compiled
word/optimized-kernel refinement, and complete failure/retry/publication
simulation remain release obligations. Existing C1 negative regressions
are preserved. No new hiding assumption, full privacy, soundness closure
or supported-budget completion is claimed.
