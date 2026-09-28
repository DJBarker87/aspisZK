# R29: a correction identity without a beta exception

Parent: `5d529b7696df2eed18c2fad3ea7d078c08dc0e61` (R28).
Branch: `research/v8-r29-beta-uniform-correction-20260928`.

**Result:** the stronger correction passes both actual opposite-witness
audits. Its relation cancellation is a polynomial identity in beta, including
beta=0. At each retained source prefix, an additional checker constructs
preimages for all **276 directions of the required compatible target space**,
not just the two witness-derived offsets. Ten focused Lean leaves compile.

This is a host-only proof-construction change. No verifier/protocol/Fiat–Shamir
challenge, wire field, production mask generator or negative regression is
changed. The former 626-row G audit is retained verbatim under a reference
name. This is not a new hiding assumption or a completed privacy theorem.

## The stronger construction

Write P(q,w) for the source seven-coefficient relation polynomial and
s=gamma^27. R28 arranges `P(rq,wr)=0`. Instead of solving G's equations only
after multiplying them by beta, require

```
P(rq,wr) = 0
P(rq,wg) + s P(qg,wr) = 0
P(qg,wg) = 0.
```

The coefficientwise source-shaped expansion is

```
P((1-beta)rq+s beta qg, (1-beta)wr+beta wg)
 = (1-beta)^2 P(rq,wr)
   + beta(1-beta) [P(rq,wg)+s P(qg,wr)]
   + s beta^2 P(qg,wg).
```

All three terms vanish. There is **no division by beta**, no exclusion of
zero or one, and no fresh-challenge assumption. Taking the source boundary
moments gives p0 retention and

```
s(g1-g0)-(r1-r0)=0,
```

so p2 is retained too. Its former independent solve row is replaced by the
stronger polynomial constraints, but the actual p2 source assertion remains
and passes. All seven polynomial coefficients are kept, including c4.

The G solve now has 633 rows: the unchanged 619 coin/raw/point/final/balance
rows, seven ordinary-polynomial rows and seven structured-polynomial rows.
The target is `(-delta, zero earlier observations, -P(rq,wg)/s, zero)`.
Both real fixture prefixes give rank **607**, with all original equations
and source rechecks passing. R28's H1 solve remains 568 rows/rank 545.

## What “beta independent” means here

The correction matrix contains no explicit beta once the other prefix
parameters are fixed. The algebraic cancellation identity quantifies over
every beta. This does **not** make the construction an online pre-beta
simulator: alpha and the query schedule occur later in the actual transcript
and can depend on beta. Neither source chronology nor the shared-oracle law
has been replaced. No synthetic beta=0 transcript was substituted for an
actual sampler execution, and no source-wide coverage conclusion follows
from freezing the other parameters of these two nonzero-beta executions.

## Entire target-space check, not only two offsets

At a fixed prefix let L be the actual structured-mask terminal functional
on 271 coin coordinates. The source targets obey

```
L(delta)=0,
P(rq,wg)(alpha)=0.
```

The second equality follows algebraically from the zero first-fold quotient;
the retained source checks independently evaluate it in the integrated audit.
The first is explicitly checked by the actual semantic enumeration.

The checker uses these target bases:

- **270 semantic directions:** for i=1..270, `e_i-L_i/L_0 e_0`.
  The source L_0 is computed and checked nonzero; its structured formula is
  the retained half^10 coefficient.
- **Six cross-polynomial directions:** `X^i-alpha^i`, i=1..6.
  These span all degree-at-most-six polynomials vanishing at alpha. They do
  not incorrectly require the cross-polynomial boundary to be zero.

For each of the two public prefixes the optimized checker performs one
633-by-1022 elimination with 276 right-hand sides. It constructs all 276
preimages and verifies **174,708 original matrix equations**, followed by
actual source coin extraction, structured terminal, raw/point/OOD/balance,
Final256 and both complete polynomial checks for every preimage. It rejects
276 corrupted-preimage controls per prefix. This is finite, exhaustive basis
coverage of this target subspace at those fixed matrices, not a random-target
test or a source-wide rank theorem.

Each complete public right inverse is 4,513,152 bytes, retained on the NUC at
`aspis-r29-g-capacity-20260928-a/check-a/world{0,1}/right-inverse.bin`.
The collector checks its hash and length against the committed certificate
receipt. The repository retains the small receipts and deterministic source
generator rather than duplicating these public binary matrices. This is not
a Lean kernel replay of their contents.

## Actual source integration

Both complete opposite-selected-input audits pass after the stronger G
correction, including:

- same public statement and actual C1/H1 helper reconstruction;
- semantic initial claim plus all 270 sent semantic coordinates;
- actual p0/p2 channel messages;
- all seven first-relation coefficients and Final256;
- source encoding/raw openings, point/OOD observations and independently
  decoded G quotient;
- fresh host verification of the unchanged honest proof bytes.

These remain fixed-prefix witness corrections; commitment roots/frontiers
are not equated and no complete alternate proof is emitted. The two honest
proof hashes remain the R27/R28 hashes recorded in the evidence receipt.

## Focused formal boundary

`BetaUniformCorrection.lean` compiles seven leaves: the beta expansion,
coefficient cancellation, all-seven cancellation, p2 retention, left/right
linearity of a finite coefficient kernel, and cancellation of the folded
coefficient itself. Its `sourceKernel` describes the per-chunk reversed dual
`[w0,w3,w2,w1]` and quarter factor. The finite-sum linearity is proved, not
postulated. The Rust array/loop/field-to-model refinement is still separate.

`CompatibleTargetBasis.lean` compiles three leaves: the pivot basis vector
is zero, all other basis vectors satisfy the covector equation, and every
compatible target is their indicated linear combination. Together with R28's
retained linear certificate-lifting theorem, this supplies the mathematical
basis-completeness argument used by the 276-target checker. It does not assume
that the actual source matrix has those preimages at every prefix.

All ten final `#print axioms` reports use only subsets of `propext`,
`Quot.sound`, `Classical.choice`; no `sorryAx` or new security axiom.
The basis file has one harmless unused-Fintype warning on `pivot_zero`.

## Exact execution receipts

Base revision as above; cached NUC Lean 4.31 and Rust release/offline/locked,
jobs 2, overflow checks enabled. Expected heavy work was the named matrix
construction/elimination and source semantic enumeration, not debug execution.
Rust scopes: MemoryHigh 5 GiB, MemoryMax 7 GiB, MemorySwapMax 0. Lean scopes:
2/3 GiB, swap 0; concurrent reservations never exceeded 10 GiB. No cold
dependencies, complete formal manifest, SBF build or unchanged CU suite ran.

| Target | Exit | Wall | Peak RSS (KiB) | Swaps |
|---|---:|---:|---:|---:|
| Integrated host compile | 0 | 25.68 s | 517,972 | 0 |
| Actual affine world0 | 0 | 35.09 s | 261,892 | 0 |
| Actual affine world1 | 0 | 36.23 s | 261,748 | 0 |
| G-capacity compile | 0 | 18.89 s | 517,212 | 0 |
| 276-target world0 | 0 | 5.75 s | 35,200 | 0 |
| 276-target world1 | 0 | 5.74 s | 35,728 | 0 |
| BetaUniformCorrection final seven leaves | 0 | 1.46 s | 1,741,684 | 0 |
| CompatibleTargetBasis three leaves | 0 | 1.39 s | 1,724,368 | 0 |

The initial four-leaf beta identity compiled before the source-shaped
bilinearity extension (1.31 s, RSS 1,620,552 KiB); the final seven-leaf run
was justified by that source change. No failed run is counted as proof.

Evidence: `evidence/r29-beta-uniform/`. Check it with

```
python3 docs/research/v8-full-view-zk-20260912/tools/check_r29_evidence.py
```

## First remaining source proposition

Establish the required H1 and beta-independent G target coverage for every
eligible source prefix, or supply a source-valid exceptional set with a
justified quantitative bound. The G part is now precisely:

> For every compatible pair (delta, h) with L(delta)=0 and h(alpha)=0,
> find a legal G quotient whose semantic coins are delta, whose retained
> raw/point/OOD/final/balance observations are zero, whose ordinary polynomial
> is h, and whose structured polynomial is zero.

This is sufficient alongside R28 H1 coverage. Requiring uniform rank 607
even where the necessary source target space degenerates would be stronger
than required; it must not replace actual target compatibility by assumption.
The explicit beta=0 rank-collapse obstruction from the old solve is avoided
by this construction **if these coverage premises hold**, not by bounding its
frequency or claiming a source-valid zero-beta trace has been checked.

Posterior-preserving adaptive transport, coherent pre-beta extraction,
shared-oracle/seed/commitment correspondence, retries/publication and explicit
security losses remain separate. C1's negative regression, fixed-block
hiding and this compatible-image calculation remain distinct.

**No CU saving is claimed:** the selected verifier is unchanged at
**1,620,236 / 1,621,719 CU**, with the actual 1M gate still open. Full privacy,
soundness and deployment readiness are not established.
