# R17 posterior counting and actual-prefix H1 coverage

Date: 2026-09-20. Base `c0cb2f8bfc3d40baa47ee68ef8c65abecac301d0`
plus this changeset. No production or staged protocol source changed.

## What is proved, and what is not

`AffinePosterior.lean` reuses `AspisV8H1C2.FiniteTransport` rather than
introducing a different probability model. For a fixed additive observation
map f, a correction delta with `f(delta)=a-b` translates every coin vector
so `f(x+delta)+b=f(x)+a`. It supplies an equivalence of every observation
fiber, equal fiber counts and `SameUniformLaw` under uniform finite coins.
It also composes the prior compatible-image lemma with this counting
argument for the joint observation `(H view, G view, H shared + G shared)`.
Coverage, consistency, compatible offsets and additivity remain explicit
premises. This is not a proof that source coins conditioned on a transcript
are independent/uniform.

Using that same-map theorem alone for a witness change would be insufficient:
hidden C1 differences can change H1's semantic map. `ContextShear.lean`
therefore permits different maps `left(h)` and `right(h)`. Its reversible
coin transformation is

`(h,g) -> (h+dh, g+dg(h))`.

The inverse first recovers `h`, then subtracts that same `dg(h)`. The source
obligations are exactly:

1. `Hview(dh) = leftOffset.H - rightOffset.H`;
2. `Gview(dg(h)) = leftOffset.G - rightOffset.G` for every h;
3. `Gshared(dg(h)) = left(h) - right(h+dh)
   + leftOffset.shared - rightOffset.shared` for every h.

When these hold, the complete listed observations commute with the
bijection and their uniform finite laws agree. No linearity of `dg` or
identity of the two H semantic maps is required. This translates existing
coins rather than resampling a mask after it has been observed. Constructing
the correction from the source-compatible image remains necessary; naming
these equations does not establish them.

## H1 coverage at the actual two source prefixes

The existing H1 diagnostic now accepts the same checked-in public-prefix
records as G. Both real prefixes give:

- 1022 quotient coordinates with OOD zeros already parametrized;
- rank 215 for 214 active-row zeros plus inactive balance;
- 807 kernel directions, every one accepted by the actual H1 pad function;
- rank 325 for 347 raw/three-point/Final256 observations, exactly accounting
  for the 22 independently checked fold equations.

RREF zero remainders and original pivot inverse products are retained.
The original synthetic test remains; its computation was factored into a
parameterized helper, not replaced. Actual-prefix input parsing is shared
with the G test. These are two fixed-prefix coverage certificates, not an
adaptive rank bound or the H1 semantic-coordinate construction.

## Focused evidence

Rust commands use offline, locked, release, jobs=1 and explicit ignored
test `r17_actual_source_prefix_h1_compatible_image`, with
`ASPIS_R17_PUBLIC_PREFIX_LOG` set to each
`evidence/r17-world{0,1}-public-prefix.log`.
Lean uses the retained `/Users/dominic/ZK/AspisFormal` cache,
`lake env lean -j1 -M1800`, and `target/r17-lean` for local outputs/imports.
The old finite-transport leaf was compiled because its object was missing
from this focused cache; no unchanged full regression was run.

| Exact target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| `AspisV8H1C2/FiniteTransport.lean`, missing local object | 0 | 8.55 | 1294303232 | 0 |
| `AffinePosterior.lean`, affine endpoints | 0 | 1.98 | 1343553536 | 0 |
| `AffinePosterior.lean`, added joint composition | 0 | 5.35 | 1370996736 | 0 |
| `ContextShear.lean` | 0 | 4.75 | 1364279296 | 0 |
| H1 actual world0 | 0 | 26.52 | 548257792 | 0 |
| H1 actual world1 | 0 | 4.97 | 80887808 | 0 |

All six audited affine/joint declarations and all three shear declarations
use only subsets of `propext`, `Classical.choice`, `Quot.sound`; no sorry or
new security axioms. The reused finite-transport audit has the same three
standard axioms. Logs under `/tmp/aspis-r15-host.drHYn9/`:
`r17-finite-transport-cache.log`, `r17-affine-posterior-lean.log`,
`r17-joint-affine-posterior-lean.log`, `r17-context-shear-lean.log`,
`r17-actual-h1-world0/1.log`.

## Next source obligation

Implement the actual H1-to-semantic-coordinate map from the staged
prover's terminal evaluations, retaining the mu^2 inactive term and the
eta-after-initial ordering. Check its semantic-terminal and compact-relation
compatibility equations, then construct the correction required above.
The H1 terminal coefficient at the final point depends only on retained
C1 point data and public challenges, but its values at intermediate
enumeration points can differ between hidden C1 contexts; they must not be
identified by assumption.

Even after that fixed-prefix construction, the adaptive exceptional-event
bound and source shared-oracle/commitment/seed law are separate obligations.
Visible failure/retry/publication behavior and malicious-prover soundness
remain open. No full privacy or deployment-readiness conclusion follows.
