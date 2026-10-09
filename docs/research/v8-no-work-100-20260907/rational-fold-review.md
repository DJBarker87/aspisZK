# Constructed rational folds for polynomial raw words

Research base: `edb199c12fcc41f00330298b95b4736f60ac6f3a` on
`research/v8-no-work-100-20260907`. This is a new restricted recovery class,
not a global V8 soundness result. Production and the selected wire are
unchanged.

Continuation: [the current far-final and extraction report](far-final-continuation.md)
records the subsequently completed divisibility, OOD, coordinate and causal
moment leaves. The earlier next-step statements below describe this first
algebra/degree checkpoint; they are superseded by that dependency map.

## Newly constructed interface

`ChordRationalAlgebra.lean` works in the actual low-bit natural basis
`[1,y,x,xy]`. For a chord `a+b*x+c*y`, it constructs the four-entry
adjugate and its norm, proves their product is the scalar norm, and clears
all four signed quotient denominators. It then proves that the resulting
four-slot vector feeds the existing V7 natural-coefficient fold exactly.
The quotient representation is therefore a theorem, not an assumed
polynomial image of an arbitrary received oracle.

`ChordRationalDegree.lean` changes to the radial variable `s=x^2`, with
`t=1-s`. The norm has degree at most two. The first three adjugate entries
have degree at most one and the fourth is constant. Consequently a raw
polynomial whose four coefficient lines have degree at most 255 produces a
cleared folded numerator of degree at most 257. The proof retains the
constant fourth entry; treating all four entries as degree one would lose
the tight bound.

For any degree-at-most-255 final polynomial, a nonzero cleared discrepancy
can agree with the rational fold at no more than 257 nonpole radial
positions. If the norm polynomial is nonzero, it contributes at most two
additional pole positions. The resulting possible-match cap is **259**.
This is a direct root bound on the constructed numerator, not a query-only
assumption and not the false same-support recovery statement.

## Scope and missing causal implication

The result applies only when the 29 raw component words already combine to
four polynomial coefficient lines of the stated degree. It does not cover
arbitrary non-polynomial helper or C1 oracles. It also does not yet establish
that four challenges with identically cleared folds force correct OOD data.
That step needs the partial fold-recovery theorem plus a source-shaped
identity showing `L*Q+I` is the committed original polynomial and hence has
the supplied values at both OOD points.

The radial variable is not definitionally the deployed final coordinate:
the latter is `T2(x)=2*s-1`. The degree leaf proves the generic affine inverse,
injectivity when two is nonzero, evaluation of the polynomial substitution
and preservation of the degree cap. The remaining source task is to identify
the selected final-domain indices with that proved affine map, rather than
merely asserting that the two coordinate conventions correspond.

If those missing interfaces are proved, a candidate local screen is

```
3/k + 22/(k-1) + 18/k + choose(259,22)/choose(262144,22),
k=(2^31-1)^4,
```

or about **118.573735 bits**. The terms are respectively a proposed
at-most-three exceptional-fold class, the general shifted degree-22 query
batch, three later degree-six repairs and query agreement. This number is
recorded as **arithmetic verified, theorem applicability unresolved**. It is
not entered as global ledger credit, and those repair terms must not be
double-counted when the causal theorem is eventually composed.

The exact arithmetic is reproduced by:

```sh
python3 -B docs/research/v8-no-work-100-20260907/experiments/chord_rational_bounds.py
```

## Focused evidence

The algebra leaf's v1 failure was confined to vector-reduction glue. Its v2
replacement uses explicit finite-vector reduction and passed in 19.76 s at
5,568,364,544 bytes peak RSS, zero swap. All eight printed declarations use
only `propext`, `Classical.choice` and `Quot.sound` or subsets.

The degree leaf was developed by symbolic bounds, never concrete QM31
normalization. Its v13 check passed in 7.79 s at 5,594,136,576 bytes peak RSS,
zero swap. All fourteen printed declarations use only the same standard
axiom subset. Source SHA-256 is
`78ec897e6940b5c5e2fb24728734b72841cf80571ea5408d49f7cb82d804a25b`;
olean SHA-256 is
`53a1484ff6093794722940892b5d4c110cbb4d7fde5fe7e07008b714aa88fd2a`.
Failed intermediate logs are kept because they identify parser keywords,
type inference and multiplication-order proof glue; no cap, premise or
mathematical bound was changed to resolve them.

No SBF build, proof generation, witness extraction, production edit or full
manifest replay was performed. The proof body remains exactly **40,282
bytes**. Full-view zero knowledge, the resource-bounded Fiat--Shamir lift,
authentication/replay and complete-transaction CU parity remain separate
open gates.

## Decision

This restricted class is worth completing: unlike a bare radius cutoff, it
uses actual rational quotient structure to force a very small matching set
for every false final. It cannot replace the arbitrary-oracle recovery task.
The next decisive formal step is the four-fold/OOD contradiction on the
actual final-coordinate domain; success would turn the presently conditional
259-position screen into a causal theorem for polynomial raw words with wrong
OOD answers.
