# R44: a normalized section for every distinct query-root tuple

Parent `29ad29d3bfbf1bf0e0e527f4a2c1afd40f6aed48` (R43).
Branch `research/v8-r44-normalized-query-section-20260929`.

**Result:** 43 new Lean theorems compile. In the exact QM31 tower, for every
injective 22-root tuple, the selected normalized directions have the same
invertible residual matrix at R43's fixed algebraic specialization. They
also preserve raw values, the final fold, and all 271 sparse G reads in the
retained source-shaped natural-basis/fold/chord model.

This is a universal-root **fixed-specialization algebraic section**, not a
full source privacy theorem or a statement about an accepted transcript.
No verifier/protocol, masks, transcript, commitments, sampler, or negative
regression changed. There is no new Rust or SBF execution. The selected
endpoint remains **1,620,236 / 1,621,719 CU**; both actual 1M-cap runs exhaust.

## Construction and exact claims

For injective `t : Fin 22 -> F`, reuse R16's natural-basis evaluation
surjectivity, proved from the natural coefficient matrix and Vandermonde
invertibility. For a selected degree `d`, choose the unique low vector
`r_d : Fin 22 -> F` whose evaluation agrees with `E_d` on the roots. Set

```
v_d = E_d - extendLow(r_d).
```

`NormalizedQuerySection` proves:

- the interpolation equations and uniqueness of the low remainder;
- `v_d` agrees with the degree-d unit at every coefficient index >=22;
- evaluation is zero at all 22 roots;
- the represented polynomial is divisible by the product of their distinct
  linear factors.

This uses the maintained `naturalLinePoly` and `naturalLineValue`, not a
monomial surrogate. `CircleNaturalBasisEval.lean` is copied byte-for-byte
from the pinned `AspisFormal` source into the focused research workspace.
No root recurrence or huge concrete natural-basis polynomial is expanded.

For slot `s`, form

```
q_d,s(block, k) = v_d(block) * (1[k=s] - alpha^s * 1[k=0]).
```

`NormalizedQuotient` proves that every coefficient block satisfies
`A + alpha*B + alpha^2*C + alpha^3*D = 0`. Each channel vanishes at every
query root, so all four raw-slot changes are zero. The actual retained
two-butterfly formula gives a zero final fold at every point with the
required nonzero x/y denominators, not merely at the queries.

The selected directions are unchanged from R43: B/C/D at degrees 24..27,
and D at degree 31. Their high coordinates therefore satisfy R43's
arbitrary-low-repair invariant.

## Exceptional degree 31 and the sparse G core

The new `HighQueryGCore` checks two small **index-only** statements against
the ten-step source carry schedule:

```
64 is not in targets(62)
64 is not in targets(targets(63)).
```

Weights stay symbolic. These facts show that the chord images of quotient
units 124 and 127 both vanish at code coordinate 128. Hence
`unit127 - alpha^3*unit124` does too. Its support bound makes it zero at
all subsequent sparse reads 131,134,...,938. No blanket permission for the
other degree-31 channels is introduced.

The degree-24..27 directions are below 112, so the generic chord growth
bound handles all their G reads. A repair below 88 has chord support below 91,
and therefore cannot change any of the 271 reads.

`NormalizedGCore` proves the actual flattening order `4*block+slot` and
composes these facts with the normalized quotient. Its G-zero theorem is
generic in the field, alpha and chord coefficients. It retains both finite
scatter lengths 512/513 and the source's zero extension.

This proves **G-core preservation**, not that every residual observation
of G vanishes. R43's essential first sparse-G boundary weight remains in
the residual matrix; none of the four coefficient discrepancies from
omitting that weight is waived.

## Exact field lift and terminal theorem

`HighWitnessFieldTransport` maps all point and polynomial observations,
including the G boundary term, through a ring homomorphism. An injective
embedding preserves the checked nonzero determinant.

`QM31NormalizedSection` uses the retained exact M31 -> CM31 -> QM31 tower
and its existing injective embedding. It proves

```
matrix(t) = map(embed, R43_fixed_matrix)
det(matrix(t)) != 0
```

for **every injective exact-QM31 22-tuple**, and hence surjectivity of this
selected 13-dimensional residual matrix. No root-distribution, oracle-law,
new hiding, or assumed nonsingularity premise appears.

`NormalizedSectionBoundary.fixed_query_section` joins nonzero determinant,
root-zero channels, coefficientwise fold-zero and all 271 G reads for the
same columns. Separate compiled wrappers give the four raw-slot equations
and the zero two-butterfly final value.

The matrix still uses R43's algebraic specialization
`z=[0,0,0,1,1,0,0,1,0,2], kappa=5, alpha=7, u=2, v=3`.
Those base-field OOD parameters are **not an accepted source prefix**.
This is the witness needed for a future polynomial nonvanishing argument
with the query roots held fixed, not that argument's full source theorem.

## First remaining source-specific proposition

For each actual distinct source query schedule, identify the executable
normalized remainder with this unique low interpolation remainder, and
transport the resulting quotient through the actual chord and T163 inverse
to a **legal active, balanced G-table correction**. The composed theorem
must retain the actual OOD/image conditions and identify all source residual
observations, including the degree-31 boundary contribution.

R44 supplies the normalized raw/final/G-core section and its fixed matrix;
it does **not** supply that complete source-mask/image refinement. A source
remainder satisfying the same evaluation equations is unique, but those
equations still need to be justified for the actual executable construction.
The source root map's retained exhaustive distinctness check is not silently
promoted to a Lean extraction theorem.

Next, define the new challenge-dependent residual polynomial for each fixed
query tuple, prove its specialization is this matrix, and derive its degree
in the remaining challenges. The old polynomial's degree 1105 is not asserted
for this new construction without that derivation.

After these steps, source shared-oracle conditional laws, first-hit/freshness,
bounded failures, retry/publication accounting, H1 joint coverage, the full
compatible-image dependencies, the adaptive posterior simulator, coherent
pre-beta extraction, and seed/commitment hops remain. In particular, the
Schur RHS `b - B*A^-1*a` must still be retained. **Full privacy and global
soundness closure are not established.** No field-size probability fraction
or claim of independence is introduced here.

## Compilation, failures and evidence

| New component | Theorems |
| --- | ---: |
| Natural-basis normalized interpolation section | 8 |
| Quotient/root/fold identities | 9 |
| Fixed-witness field transport | 4 |
| Exact-QM31 normalized matrix | 6 |
| Exceptional G boundary and source-shaped support | 8 |
| Flattened normalized G-core composition | 4 |
| Joint boundary and exact-QM31 raw/final wrappers | 4 |
| **Total** | **43** |

The final successful new theorem leaves total **10.99s**. Including the
six retained prerequisite compilations and explicit retained-axioms audit,
the selected successful targets total **18.65s**, peak RSS **2,466,860KiB**,
swap 0. All 43 new audits and 19 retained audits use only `propext`,
`Classical.choice`, and `Quot.sound` (some use a subset).

The NUC used serial 3G/5G/no-swap scopes with TasksMax 128 and the existing
Lean 4.32 dependency cache. Before launch it had 62GiB RAM and 44GiB available;
the old 7.5GiB host swap occupancy was not consumed by these no-swap jobs.
No package-wide/cold build or unchanged runtime regression ran. The final
cache contains 211 source/toolchain-checked objects.

Failures are preserved, including local finite-index/conditional-rewrite
plumbing, a looping broad simplifier in the field mapping, and wrapper
elaboration timeouts. The map proof now uses explicit case splitting. The
wrapper timeout is fixed by a generic evaluated-fold lemma and a named
coefficient-to-final theorem, keeping the quotient opaque; the final wrapper
compiles without raising heartbeats/recursion or memory limits. The final
two unused-premise/simp-argument warnings do not suppress any check.

Commands, source revisions/hashes, exit statuses, per-target wall time/RSS/
swap and axiom output are in `evidence/r44-normalized-query-section`.
The 44-artifact manifest and 215 source/evidence pins are checked by

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r44_evidence.py
```

The 211 cached sources are independently checked against their successful
metadata. R43's source checker/witness pins are retained as evidence inputs;
no new Rust execution is claimed. No merge, deployment, or wallet operation.
