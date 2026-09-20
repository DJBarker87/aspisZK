# R17 explicit H1 two-OOD coverage

Date: 2026-09-21. Source base
`d7692b0cc370825768741d06ef0e3ba1a7bdb657` plus this changeset.

## Universal algebra replacing one rank condition

For distinct points p0=(x0,y0), p1=(x1,y1), select t=y if y1 differs
from y0, otherwise select t=x. The selected difference t1-t0 is nonzero.
For any two targets v0,v1, choose

`b=(v1-v0)/(t1-t0)` and `a=v0-b*t0`.

Then `a+b*t0=v0` and `a+b*t1=v1`. `OODPair.lean` proves this construction
over any field and proves that evaluation of the span of 1,x,y surjects
onto both values for **every distinct pair**, not merely a tested prefix.
It does not need random challenges, distinct y coordinates, nonzero x/y,
or a circle equation.

In the research source's natural circle basis, indices 0,1,2 are 1,y,x.
The immutable R16 transport starts with common legal inactive mask rows.
For j in {0,1,2}, the balanced direction
`e_(order[j]) - e_1023` maps to coefficient basis vector e_j. Consequently
two of these directions supply the interpolation, with no active-row
change. The earlier `BalancedTransport.lean` gives the generic balancing
and exact-target-lift algebra; its Rust array/field refinement is not
silently claimed complete here.

`r17_h1_two_point_pad` now implements this construction instead of solving
a 2-by-809 system. It checks the exact transformed coefficient vector,
actual H1 padding acceptance and both source OOD evaluations. It returns
None on coincident points rather than dividing by zero. The caller tests
both coordinate branches using distinct circle points and retains a
coincident-point rejection control before correcting the real helper.

## Source distinctness and scope

The staged `inactive_row_binding.rs::to_gamma` samples the first OOD point,
absorbs its vector, then tries up to three samples for a **different**
second point. Otherwise it returns `Error::Sampler`. Thus successful
prefixes already satisfy the needed distinctness. The new correction
neither changes that chronology nor hides the failure branch.

This removes an additional algebraic rank-exception condition for the
first H1 OOD correction on successful prefixes. It does **not** assign zero
probability to source sampler failure, prove a seed/oracle law, or repair
the other coverage gaps. The remaining lower-rank obligations are C1's
108 rows per column, H1's joint rank 540 and G's rank 601, together with
universal affine-target compatibility and explicit exceptional-event
bounds. Full privacy and soundness preservation remain open.

## Focused verification

`OODPair.lean` compiled in `/Users/dominic/ZK/AspisFormal` with the existing
cache, `lake env lean -j1 -M1800`, local r17/r16 imports and an explicit
output object. Both `#print axioms` results list only propext,
Classical.choice and Quot.sound; no sorryAx. Three style-linter warnings
are nonfatal. No dependent source file was changed and no full manifest
was replayed.

The v19 host build uses the retained cache and
`cargo build --offline --locked --release --jobs 1` with the exact stage
flags/features. Runtime uses the honest fixture, selectors 0 and 1,
`ASPIS_R17_C1_WITNESS_AUDIT=1`, `NO_DNA=1`, with live/complete contexts and
oracle/nonce/scan overrides unset. The changed OOD pad is exercised through
the full downstream witness correction; this is not an unchanged replay.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| OODPair.lean | 0 | 8.55 | 1366736896 | 0 |
| v19 host build | 0 | 49.29 | 735854592 | 0 |
| v19 world0 complete witness correction | 0 | 34.53 | 288423936 | 0 |
| v19 world1 complete witness correction | 0 | 34.11 | 288473088 | 0 |

Both directions pass the new branch/rejection checks and all existing
C1/H1/G, source-initial and ten-round semantic checks. The original
emitted proofs retain SHA-256
`a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5`
and `e81cd45d977e56ce4c5307dc792a468b182dc2d44b2722670aa0a140a38613a7`.
That checks audit transparency, not equality of full transcript laws.

Metrics are from `/usr/bin/time -l`. Artifacts under
`/tmp/aspis-r15-host.drHYn9`: `r17-ood-pair-lean.log`, `r17-build-v19.log`,
`r17-v19-world0.log`, `r17-v19-world1.log`, and stage
`r17-two-channel-source-v19`. Its manifest SHA-256 is
`b6954128f7f09e9e75bcb2271c474e2749645262472bfc676126ec08b9825145`.
No source pins or negative regressions were waived or removed.
