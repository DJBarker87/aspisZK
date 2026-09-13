# R3 public-coset simulator boundary

Date: 2026-09-13.

The Rust affine module now constructs a witness-free representative of
`L*y=c(x,h)`, after checking both `L*M=0` and
`rank(L)+rank(M)=dim(observation)`. It then samples `y0+M*r` from explicit
ideal M31 coins. Missing quotient rows, non-annihilators, inconsistent right
hand sides and coin-shape mismatches fail closed. The simulator API receives no
witness.

The focused transport regression uses three distinct offsets in one public
coset and checks the explicit coin translation pointwise. The Lean leaf proves
the corresponding kernel/range correction, affine transport, and bijectivity
of coin translation.

## V8 source boundary

For the fixed spread raw-C1 schedule, the observation map has full row rank,
so its quotient is trivial and this constructor gives an ideal-tape simulator
for that isolated raw block. This does not simulate the real view: the same
field seed has already influenced roots, helper values and semantic messages,
and the real schedule is transcript-derived.

No source function or theorem currently supplies `c(x,h)` for the nontrivial
quotients of the complete V8 view. H1/C2, salted roots, semantic/relation
sumchecks and adaptive oracle stages also remain outside the affine sampler.
Calling the real prover to obtain an offset would use the witness and is
forbidden.

R3 therefore closes the constructive fixed-affine boundary but leaves the V8
single-attempt simulator blocked at the first unsupported nonlinear/helper
stage identified by R1. This is an exact missing theorem, not an unassigned
implementation detail:

> For every valid witness and reachable pre-C2 public history, construct from
> public data a causal law for H1/C2 and the semantic messages, coupled to the
> already committed C1 root, with an explicit distance bound and no access to
> the hidden trace.

Without that theorem, neither R3 nor full-view privacy can be promoted.
