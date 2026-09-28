# R27: what the six first-relation rows do and do not imply

This is a source-grounded **conditional arithmetic bridge**, not a proof that
the actual 626-row correction system has a solution at every source prefix.
The runtime source, sampler and all seven-coefficient negative checks remain
unchanged. No new hiding or nonzero-beta assumption is introduced.

## Exact source inventory

`tools/bind_r27_boundary.py` checks all 182 selected-stage pins and records
the exact hashes/equations of eight source files in
`evidence/r27-sparse-preparation/boundary-source/binding.json`:

- `sumcheck.rs`: `accumulate_chunk` convolves q with reversed dual weights
  `[w0,w3,w2,w1]/4`; `boundary_sum` is **4(c0+c4)**, not a Boolean endpoint sum.
- `field.rs`: `M31_QUARTER=536870912`; its product with 4 is 1 modulo P.
- `r17_c1_witness_audit.rs`: six coefficient rows at indices 619–624 select
  `[0,1,2,3,5,6]`; row 625 is the difference-functional p2 equation. The code
  separately asserts p0 retention and later checks all seven coefficients.
- `r17_coupled_audit.rs`: legal q tails are `[b*x,c*x,0]` at 1021–1023.
- `r17_opening_weights.rs`: original G weights are inactive indicator plus
  kH+k²E1+k³E2; image weights contribute t*q1023+tt*(b*q1022-c*q1021).
- Host relation, callback and transcript sources: beta is sampled after the
  channel coefficients with `sample(...,false)` and the ordinary QM31 sampler
  accepts zero limbs. No nonzero-beta promise is available from this path.

Matching text and hashes is **not** a Rust-to-Lean semantic refinement proof.
The algebra below states its required moment and polynomial correspondences;
the retained source tests and earlier dual/chord results are not silently
promoted into a new universal machine theorem.

## Conditional implication proved

Write s=gamma^27 and use the actual source quotient corrections rq,qg:

```
r0 = <rq,wr>     r1 = <rq,wg>
g0 = <qg,wr>     g1 = <qg,wg>
dp2 = s*(g1-g0) - (r1-r0)
```

For wb=(1-beta)wr+beta*wg, the boundary of the combined correction polynomial
is algebraically

```
(1-beta)*((1-beta)*r0+beta*r1)
  + s*beta*((1-beta)*g0+beta*g1)
= (1-beta)*r0+beta*s*g1-beta*(1-beta)*dp2.
```

Thus p0 retention (`r0=0`), the zero G functional (`g1=0`), and retained p2
(`dp2=0`) force zero combined boundary **for every beta**, including zero.
The G functional is zero if its inactive/H/two other point moments vanish
and the legal q image equations hold. The source's `[b*x,c*x,0]` tail makes
the image residual zero by commutativity, without dividing by b or c.

The source convolution's boundary is its input dot product; the formal
chunk identity checks the reversed-weight/factor-1/4 convention. If the six
sent coefficients vanish, c0 vanishes. With 4 nonzero, `4(c0+c4)=0` then
forces c4=0, and hence all seven coefficients vanish. This justifies the
omitted-coefficient implication under these premises. It does not construct
rq or qg satisfying them.

## Necessary zero-beta case, not an asserted attack

At beta=0 each G coefficient row 619–624 is zero. For a fixed R correction,
the combined coefficient is then just the R coefficient; if it is nonzero,
no G correction can cancel it. `zero_beta_obstruction` proves that scalar
statement without assumptions on the G value or gamma scale.

This does **not** prove that such an R correction occurs at an admissible
source prefix, that every legal H1/R choice fails, or that an attacker obtains
a distinguishing advantage. Those require further source work. It does rule
out claiming universal feasibility from the boundary identity alone. Next,
establish that an appropriate legal H1/R correction exists at such prefixes,
or characterize the source-valid exceptional event and justify its probability
under the actual shared-oracle law. No fresh-uniform/IID probability bound is
claimed here. Other possible rank-degeneracy cases remain open too.

## Exact formal result

`lean/AspisV8R19/FirstRelationBoundary.lean` compiles eight declarations:
`chunk_boundary`, `boundary_identity`, `boundary_zero`, `missing_four`,
`source_quarter`, `structured_moment_zero`, `all_seven`,
`zero_beta_obstruction`.

Final focused run: **exit 0; wall 1.47s; peak RSS 1,687,752 KiB; swap 0**,
cached Lean 4.31, parent `7f1421807da7d7aeefebf1ba6d6355d794f81e3b`.
All `#print axioms` reports contain only subsets of `propext`, `Quot.sound`,
`Classical.choice`; no `sorryAx`.

Retained predecessors: an unavailable FieldSimp cache import (exit 1, no cold
build attempted), a rewrite-order error (exit 1 with failed-declaration
`sorryAx`, not accepted), and the successful seven-leaf predecessor (exit 0,
1.42s, RSS 1,686,156 KiB). The final run is justified by adding the explicit
zero-beta obstruction theorem, not an unchanged full replay.

**First remaining full-privacy proposition remains universal source joint-image
compatibility (or a justified source exception bound), followed by a posterior-
preserving adaptive correction/simulator.** Coherent pre-beta extraction,
shared-oracle/seed/commitment correspondence, retries and publication are still
separate obligations. Fixed-block hiding, C1's negative regression and these
local algebraic facts remain distinct from full-transcript privacy.
