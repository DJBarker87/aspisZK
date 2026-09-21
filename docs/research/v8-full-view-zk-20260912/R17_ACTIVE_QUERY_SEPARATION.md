# R17 active-row separation from query corrections

Date: 2026-09-21. Base
`d0ceb5a2dfe373e6871ca52853d11ec66d4ca98a` plus this changeset.

## Fixed source geometry

The active original rows become 214 coefficient positions under the
immutable transport. The first is 100, the last is 1018. Counting active
positions in each block of four gives the histogram
`[110,92,40,14,0]` for blocks containing 0,1,2,3,4 active positions.
In particular, no block has four active positions. The new layout test
checks these exact source facts without sampling challenges or schedules.

`r17_low_quotient_correction_preserves_active_rows` checks all 88 low
quotient basis directions against each of the three chord-coefficient
basis directions. Every product has support at indices <=90, strictly
below the first active position. Inverse transport and the actual H1 pad
routine accept all 264 resulting messages. The chord product is linear in
the quotient and in its three chord coefficients; these are complete basis
checks of that finite low-support component, not a random sampling test.
A full formal Rust linearity/index refinement is still not claimed.

## Why the query-dependent low tail can be separated

The compiled compatible interpolation theorem, specialized to zero final
polynomial and n=m=22, constructs all four quotient channels at degree
below 22. Thus a raw correction within final-zero space uses only the first
88 quotient coefficients. Multiplication by the chord cannot reach an
active coefficient under the source geometry above. The correction is
also balanced because its encoded coefficient 1023 vanishes.

Consequently raw values can be corrected without changing active rows.
This is a structural deduction using the interpolation theorem and the
source support calculation, not a new joint privacy claim. It also does
not assert that the three point claims are unchanged by the low correction.

Equivalently, for the factored balanced kernel, write each channel as
P times a polynomial of degree below 233. The coefficients at degrees
22..254 are free coordinates: multiplication by the degree-22 vanishing
polynomial is triangular with nonzero leading diagonal in the maintained
natural basis. Its lower 22 coefficients are determined by the queries,
but cannot affect active rows after chord multiplication.

The test explicitly truncates the low 88 quotient coordinates in each of
the 699 factored directions and checks that every active-row value is
unchanged. It separately constructs the active matrix using only unit
channel coefficients at degrees 22..254. That direct matrix depends only
on alpha, the chord and the fixed layout; it does not use the query roots,
semantic challenge vector or witness/mask values. At both retained
prefixes, direct and factored active ranks are 214. The original full and
balanced residual-map checks remain in place.

The triangular coordinate-change/source-degree bridge has not yet been
packaged as one compiled Lean source-refinement theorem. The tested source
identities and the existing polynomial theorem are kept distinct here.

## Precise next lower-bound problem

For the 214 active constraints, it is now sufficient to prove full rank of
the direct 214-by-699 matrix as a function of alpha and the chord, outside
an explicitly bounded exceptional set. A separate nonzero-minor proof for
each query schedule is not needed for this component. The two measured
rank values are not themselves that universal probability bound.

The source rational OOD map has coordinates
`x(u)=(1-u^2)/(1+u^2)`, `y(u)=2u/(1+u^2)`.
After removing its nonzero common scale, a chord between u and v has
coefficients `[1+u*v, u*v-1, -(u+v)]`. This suggests a low-degree
determinant route using a fixed active-matrix minor. The normalized-chord
source identity, the minor/degree certificate and the actual sampler/oracle
law still need explicit justification before any numerical loss is claimed.

H1's three point claims and G's remaining semantic/point/relation maps
still depend on the queried-root factor. C1 joint coverage is also open.
None of the commitment, shared-oracle, seed, visible-failure/retry/
publication or malicious-prover soundness obligations is discharged by
this separation.

## Focused evidence

No Lean source changed or compiled in this step; no new axioms result is
claimed. Rust jobs used the retained cache, offline/locked/release/jobs=1,
package `aspis-prover`, `--lib` and the single named test with `--nocapture`.
The actual-prefix tests additionally used `--ignored` and the checked-in
prefix record selected by `ASPIS_R17_PUBLIC_PREFIX_LOG`.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| Initial active coefficient geometry | 0 | 23.71 | 559874048 | 0 |
| Complete low-support/chord basis checks | 0 | 23.87 | 562790400 | 0 |
| Geometry with exact layout assertions | 0 | 0.07 | 81018880 | 0 |
| Direct/factored active map, world0 | 0 | 5.36 | 84557824 | 0 |
| Direct/factored active map, world1 | 0 | 5.40 | 84541440 | 0 |

All metrics use `/usr/bin/time -l`. Every invocation reports one passed
test, zero failed. Logs under `/tmp/aspis-r15-host.drHYn9`:
`r17-active-geometry.log`, `r17-active-geometry-v2.log`,
`r17-low-active.log`, `r17-active-query-world0.log`,
`r17-active-query-world1.log`. No source pins or negative controls were
removed, no host proof was regenerated, and no full suite was repeated.
