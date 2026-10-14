# Reuse the circle-to-GRS conversion for efficient extraction

The repository already proves the algebraic conversion needed to apply a
standard Reed–Solomon list decoder. We do not need a new circle-code
decoding algorithm. This is a concrete algorithm route and reuse finding,
not an implemented or formally refined extractor.

## Checked conversion and exact parameters

`Wide/GRSConversion.lean` supplies `exactInitialEncoder_coordinate_grs`,
`exactInitialGRSConversion`, and `exactInitialEncoder_eq_grs`. The existing
initial encoder is a 1024-dimensional **subcode** of the polynomial
evaluation space of degree at most 1024, on 1,048,576 distinct points.
The ambient polynomial dimension is 1025, so treating its degree as 1023
would be incorrect.

The point is the stereographic coordinate `t_i = y_i/(1+x_i)`. The
nonzero column multiplier is `v_i = (1+t_i^2)^(-512)`. The checked identity is

```
exactInitialEncoder(message)(i) = v_i * polynomial(message)(t_i).
```

The conversion proves distinct points, nonzero multipliers, injectivity of
the message-to-polynomial map, and its degree bound. A received word can
therefore be divided by `v_i` without changing any agreement set. The exact
agreement threshold is 38,230, whereas
`sqrt(1,048,576 * 1024) = 32,768`.

The standard Guruswami–Sudan algorithm lists all polynomials of degree at
most `d` agreeing at `t > sqrt(n*d)` positions. It solves interpolation
constraints, finds polynomial roots, and checks agreement. For finite
fields, polynomial dependence on the field's bit length uses randomized
factorization/root finding; the paper distinguishes this from deterministic
time polynomial in the field's cardinality.
[Guruswami–Sudan, §§1–2](https://people.csail.mit.edu/madhu/papers/1998/gs.pdf).

## Root-selected implementation route

1. Rescale each recovered received lane by the existing nonzero multipliers.
2. Run a finite-field list decoder for the degree-at-most-1024 ambient code.
3. Retain only polynomials in the exact circle-message image, invert that
   image map, and verify the 38,230 agreement threshold.
4. Merge lane candidates incrementally, pruning after each lane by joint
   agreement. The existing partial joint-list theorem bounds every retained
   family by 100, provided it is supported on the selected lanes.
5. Apply the existing semantic extraction only after its candidate and
   accepted-check premises are derived from the proof.

Steps 1–3 are our proposed application of the checked conversion to the
standard algorithm. The subsequent [exact inverse checkpoint](GRS-MESSAGE-INVERSE.md)
now supplies a finite algebraic inverse and an exact image test using the
actual encoder transformations. It retains the distinction between circle
messages and the larger ambient polynomial space. The generic
`ExactGRSConversion` record still stores injectivity rather than an
executable inverse or runtime certificate; the new separate specification
also needs executable refinement.

Step 4 avoids materializing the product of all lane lists. With at most
100 retained partial tuples and at most 100 next-lane candidates, each
merge considers at most 10,000 pairs before pruning. The subsequent
[incremental merge checkpoint](INCREMENTAL-CANDIDATE-MERGE.md) proves that
the finite loop returns exactly the old joint list given complete per-lane
lists. It also bounds a 29-lane run by 290,000 candidate pairs. This is a
pair-count bound, not a field-operation or runtime bound. The finite-set
specification still needs an executable representation and refinement.

The old multiplicity-three proof already checks an interpolation budget:
6,480,098 coefficients, 6,291,456 constraints, Y-degree 112 and weighted
degree 114,689, strictly below `3*38,230`. These counts establish the
mathematical interpolation dimension; they do not justify constructing a
dense matrix of that size or imply a practical runtime. No such matrix
build has been launched.

## Boundaries

The per-lane exact decoder specification still uses `Classical.choose` and
finite message-space filtering. The existing algorithm interface also has
a `deterministicPolynomialTime : Prop` field without an executable cost
model. We must not fill that field with a tautology or cite a randomized
algorithm as a deterministic bit-complexity proof.

An extractor with appropriately justified randomized running time is a
possible route, subject to the chosen knowledge definition and failure
accounting. No such instantiation is claimed here. This route also does not
prove the causal classifier, Fiat–Shamir composition, or zero knowledge.

The [inverse reuse inventory](GRS-INVERSE-REUSE-INVENTORY.md) records the
existing polynomial uniqueness and parity facts, and distinguishes them
from a constructive inverse of the full message-to-polynomial map.
