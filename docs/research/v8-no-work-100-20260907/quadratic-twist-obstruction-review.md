# Quadratic nonsquare-twist OOD ingredient

Parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Status: checked and frozen; nine standard-only axioms audits.

[QuadraticTwistObstruction](experiments/QuadraticTwistObstruction.lean) isolates
the X-constant parity case of the proposed quadratic discriminant split.
Over a field L, if d is nonsquare and `A^2=d*H^2`, then H is zero: a nonzero
H would make d the square `(A/H)^2`. The polynomial version uses the actual
injection `K[Z] -> FractionRing K[Z]`; nonsquareness is in K(Z), not merely
an absent polynomial square root.

The bivariate input has the source convention `Polynomial K[X]`: outer Z,
inner X. At an OOD point t, `H.map (evalRingHom t)` is H(t,Z), not H(X,t).
The square identity forces this entire polynomial to zero, so every fixed
Z coefficient of H vanishes at t. For nonzero H the selected obstruction is
its original leading Z coefficient, a nonzero polynomial E(X). It is fixed
from H before either OOD point. Both complete polynomial answer identities
force both actual points into the roots of the same E, even with sequential
adaptive answers. A supplied coefficient X-degree bound transfers to E.

The proof uses coefficient evaluation at the original index. It does not
assume that the leading degree is preserved at either point; degree drops
are therefore included in the obstruction conclusion.

The independent `atPoint_zero_iff` and `specialization_obstruction_zero`
interfaces require no nonsquare premise. Applied to an explicitly reordered
H (outer X, inner Z), the same construction gives a fixed polynomial in Z
whose roots contain the whole-H-zero gamma specializations. This does not
reuse an X-obstruction at gamma without exchanging the variables.

This ingredient does NOT construct a discriminant factorization, prove a
parity factor has X degree zero, or derive nonsquareness from primeness of
an actual quadratic factor. Those are the remaining applicability lemmas.
It also does not prove a paired OOD sampler law, a global security number,
component recovery, received-word polynomiality, or a bounded extractor.
The actual degree-two helper curve and full degree-28 claim-error timing
are not altered by this algebraic ingredient.

## Verification

The first focused attempt `quadratic-twist-obstruction-nuc-v1` passed:
exit 0, wall 1.05 seconds, peak RSS 1,953,424 KiB, zero swaps.
All nine printed declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, new axiom, increased recursion/heartbeat budget,
or concrete field enumeration was used.

```
source
b4d744dec309730da71b07250f8fbd343aedb4398cdce7db538f2c3fdf04d526
olean
1d3832ee325047c04f13d273276650df9816c3df81b4c7ebec8379c9a2416d58
manifest
7a22ff07dba58c2151fcdd426ea1681ee6b8508c730e91a543f197812ada9c2e
runner
5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52
```

The higher-Y runner checked 805 provenance entries before and after the
target and reported the overlay unchanged. It used MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, CPU 200%, Lean `-j1 -M9500`, with
the borrowed immutable V7 pin `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
All access used the verified Tailscale address `100.108.41.90`; the
`HostKeyAlias=nuc.local` option served only pinned key verification.
The exact source snapshot, manifest, log and green output are retained
locally. The build slot was released after postflight. No laptop, cold
dependency, package-wide, or unchanged-target replay was performed.
