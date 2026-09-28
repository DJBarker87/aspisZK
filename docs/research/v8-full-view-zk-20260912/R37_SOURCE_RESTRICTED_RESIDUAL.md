# R37: restrict the residual polynomial to roots and circle parameters

Parent `73cd6b03a759c06714121a90108865fc71c50cce` (R36).
Branch `research/v8-r37-source-restricted-residual-20260929`.

**Result:** a 36-variable residual polynomial now constructs its query
coefficients from 22 roots and substitutes the normalized two-parameter
circle chord. Eleven new Lean declarations compile. Both genuine prefixes
match the substituted arithmetic and its determinant scale. One explicit
algebraic specialization has nonzero executed M31 determinant 1171866436.

The specialization is **not yet a Lean-checked nonvanishing certificate**.
Neither the host witness nor the formal evaluation/scale identities prove
full privacy or a source-exception probability. No verifier/protocol change.

## Chord scaling is proved, not omitted

`ResidualHomogeneous.lean` proves that scaling all three chord coefficients
by t scales each low point weight, each polynomial coefficient, and each
residual entry by t. Consequently the selected determinant scales by t^13.
This includes the point observations as well as both relation polynomials.

It composes that result with the retained rational-circle normalization:

```
normalized chord = (1+u*v, u*v-1, -(u+v))
actual chord     = lambda * normalized chord
lambda          = 2*(v-u)/((1+u^2)*(1+v^2)).
```

With nonzero denominators, the actual determinant equals lambda^13 times
the normalized determinant. `rational_nonzero_iff` additionally uses 2≠0
and v≠u to prove their nonzero conditions equivalent. It does not assume
either determinant is nonzero.

## Root construction is inside the polynomial

`SourceResidualPolynomial.rootRun` starts with coefficient vector `[1]`
and applies the explicit R36 natural-basis multiplication followed by
subtraction of `root*p`, in source list order. Its fixed 27-coordinate
workspace contains the degrees needed for the 22-root polynomial and
subsequent four shifts. `rootCoefficients` retains coordinates 0..22.
Ring-homomorphism transport is proved for this construction.

The new polynomial has variables

```
0..9    z
10      kappa
11      alpha
12..13  u,v
14..35  22 query roots.
```

It substitutes both the root-derived coefficients and normalized chord
**before** forming the residual determinant. Its entry and determinant
evaluation identities compile. This removes the mistake of trying to
establish the desired event from a nonzero polynomial in three unrelated
chord coordinates and 23 unrelated query coefficients.

The symbolic model's universal Rust/field/loop correspondence remains a
separate obligation, including the fixed workspace's support/refinement.
R35 has the source-shaped support/leading lemmas; their complete composition
with this finite workspace is not claimed here.

## Two unchanged source prefixes

The checker reuses R36's arithmetic implementation verbatim up to its
`main`, changing only inner doc-comment markers for inclusion. That generated
fragment is pinned and independently checked against the R36 source by the
evidence gate. No arithmetic formula is rewritten for the witness test.

For each retained actual prefix it:

1. derives the 22 roots using the pinned source fibre sampler;
2. compares all 23 fixed-workspace coefficients with source `times_x` root
   construction and checks the high tail is zero;
3. recovers u,v from the original circle points and checks denominators and
   distinctness, without replacing the points;
4. evaluates the normalized residual matrix and compares all 169 scaled
   entries with the committed R36 source-checked matrix;
5. checks both nonzero determinants and the exact lambda^13 relation.

Totals: **46 coefficient checks, 338 matrix-entry checks**, two determinant
scale checks. Omitting the scale changes the matrix on both prefixes.
These are not fresh source transcripts or another privacy-frequency search.

## Explicit algebraic witness candidate

The one fixed candidate was chosen before execution:

```
z = [2,3,4,5,6,7,8,9,10,11]
kappa = 5; alpha = 7; u = 2; v = 3
roots = [1,2,...,22]
half = 1/2; quarter = 1/4 in M31, embedded in QM31.
```

The query polynomial is constructed from these roots, not freely assigned.
Its leading natural coefficient is checked equal to half^19. The normalized
chord is (7,5,-5); both rational denominators are nonzero. The computed
13-by-13 determinant is **1171866436 modulo 2147483647**, hence nonzero.
Every matrix entry and the determinant lie in the M31 subfield; canonical
limbs and zero extension limbs are checked. The 2704-byte matrix is retained.

This is an **algebraic** specialization, not a source-generated transcript.
Its roots/OOD parameters are not claimed to belong to the actual sampler's
accepted support or obey its chronology. Such a specialization can support
a polynomial nonzero theorem once kernel-checked; it cannot by itself
establish a source probability bound, negligible loss, or simulator.

## Exact receipts

Source stage `/home/dombarker/project-offloads/aspis-r37-source-20260929-b`
has 192 pins. All inherited R36 non-Cargo pins remain unchanged. The new
checker and the generated arithmetic fragment are the only added sources.

| Focused target | Exit | Wall | Peak RSS KiB | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Release/offline/locked compile | 0 | 19.40s | 517,644 | 0 |
| Two prefixes plus fixed algebraic witness | 0 | 0.01s | 1,936 | 0 |
| `ResidualHomogeneous.lean`, six declarations | 0 | 1.17s | 2,278,560 | 0 |
| `SourceResidualPolynomial.lean`, five declarations | 0 | 1.19s | 2,282,004 | 0 |

All eleven final axioms audits contain only propext/Classical.choice/Quot.sound.
Twenty-two R36 objects were reused, followed by the homogeneous leaf when
the admissibility equivalence was added. The first Rust compile rejected
inner documentation comments inside an include; its failure log is retained.
Only the generator's comment conversion changed for the successful rerun.
No memory caps were raised or package-wide manifests replayed.

Rust scope 5G/7G and Lean scope 3G/5G; MemorySwapMax0, TasksMax128;
optimized Rust with overflow checks enabled. Twenty-three public artifacts
plus their manifest are in `evidence/r37-source-restricted-residual`.

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r37_evidence.py
```

## First remaining proposition and safe certificate route

Kernel-check the explicit specialization of the **36-variable restricted
polynomial**, then use `determinant_evaluation` to prove it is not the zero
polynomial in the actual characteristic. Do not substitute the earlier
38-variable unrestricted polynomial or a matrix unrelated to the model.

The functional recurrence `rootRun` branches over 27 coefficients at each
step. Blindly normalizing its 22-step concrete evaluation would duplicate
work exponentially. The certificate route must first prove symbolic
step/aggregation lemmas, retain intermediate coefficient/point arrays,
and check one small affected cell before any complete aggregation. Matrix
invertibility can use a checked small inverse or elimination certificate;
it must also be linked to the model's evaluated entries. A matrix-only
certificate without that link is insufficient.

After nonvanishing, explicit degree bounds and the actual chronological
shared-oracle/first-hit law still need to justify the exceptional-event
loss. Current H1 coverage, full source refinement, adaptive posterior
simulation, pre-beta pair extraction, commitment/seed hops, visible failures,
retries/publication and overall security losses remain open.

Selected CU stays **1,620,236 / 1,621,719**, with both actual 1M runs
exhausting. No SBF repeat, negative-regression removal, merge, deployment,
wallet operation, or full-privacy claim occurred. The goal remains active.
