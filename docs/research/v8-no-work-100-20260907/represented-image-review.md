# Represented-final image and row game

Research source pin: `bbca32e0e30be2c489c6437dd670da164e6d852f`.
Status: **kernel-checked causal supported-event bound**, with the stated
geometry link and source/FS boundaries still explicit.
This leaf changes no Rust, proof body, transcript, masking or production path.
The maximum body remains **40,282 bytes**. No CU result follows from this work.

## New supported-event claim

Fix a reference quotient `Q` and the ordinary functional/claim before tau.
The received four-slot oracle is arbitrary, including globally
non-polynomial words. The first compact response may depend on tau, but
precedes alpha0. The final may depend on both; the ordered queries precede
rho; each later compact response may depend on its preceding challenges.

Let `Support(tau, alpha0)` be determined at the post-final, pre-query prefix.
Suppose a separate deterministic argument establishes, on that event only,
that the actual final equals `coefficientFoldLayer 256 alpha0 Q`.
The new development bounds the probability of **actual compact-tail
acceptance AND Support** in the original finite challenge experiment. It
does not condition the challenge distribution on Support.

The geometric argument being developed concurrently chooses Q from the
fixed received word, not from the actual accepted transcript. Its exact
encoder/oracle coupling is a separate dependency. A quotient chosen merely
before tau is insufficient for the shifted-row theorem: there it must be
fixed before kappa together with all four original functionals and claims.

| Fixed-prefix condition on Q | Supported accepted mass |
|---|---|
| Invalid reconstruction image (ordinary discrepancy unrestricted) | `(q+2)/|G| + 24/|A|` |
| Valid image, nonzero fixed ordinary discrepancy | `q/|G| + 24/|A|` |
| Valid image, at least one wrong ordinary row fixed before kappa | `(q+3)/|G| + 24/|A|` |
| Invalid image OR wrong rows, with Q fixed before kappa | `(q+3)/|G| + 24/|A|`, by an explicit fixed-prefix image partition |

Here alpha0 and the three later relation challenges are fresh uniform on A;
tau, kappa and rho are fresh uniform on G at their respective boundaries.
The ordered query schedule uses the existing ideal uniform distinct law.
For QM31, the intended specialization is `|A|=k`, `|G|=k-1`.
These are restricted ideal-game bounds, not a global soundness figure.

## Why no query-miss term is necessary here

Equal actual/reference finals make the constructed final-difference
polynomial zero. The existing source-shaped `same_prior` theorem then
identifies the actual incoming relation discrepancy with the reference
discrepancy. For any ordered schedule, a nonzero prior makes

```
prior - rho * sum_i residual[i]*rho^i
```

a nonzero degree-at-most-q polynomial. This remains true when all query
residuals vanish. Its root bound is q, not q-1. After this batch there are
three relation responses left, contributing `18/|A|`; the first response
contributes `6/|A|` separately. No relation repair is counted twice.

The proof does not assume pointwise query acceptance or that touching a
corrupted fibre always rejects. Legitimate rho and later-round collisions
remain in the charged bad events.

## Interface and reuse

[`RepresentedImageGame.lean`](experiments/RepresentedImageGame.lean) reuses `CausalShiftedRows`,
`CausalOrderedRelation`, `OrderedPostQueryGame`, `FirstImageDiscrepancy`
and their existing V7-consumed V6 compact sumcheck/fold interfaces.
It does not import the V7 q16 schedule, work stages or its FS resource law.

The only new geometry-facing premise is
`Support -> actual final = reference fold`.
The actual zero difference, preserved prior, shifted residual polynomial
and compact terminal relation are derived using the retained constructors;
they are not supplied as unverified scalar equalities.

`arbitraryOracle D Q ...` uses the existing `FixedOracle D D Q` type. Its
outside-corruption support requirement is vacuous because the corruption
set is all of D. Thus this proof contains no hidden global-polynomial or
small-radius premise. It still requires genuine nonzero circle coordinates
and the correct final-domain coordinate map. Root's selected received-word
constructor must supply those from the same actual R, not an unrelated oracle.

## Remaining accepted mass

The result does not bound represented, image-valid, ordinary-correct
executions in which component recovery or checked payment extraction fails.
Nor does it bound unsupported adaptive finals. Sparse eligible-alpha
branches, replay/fuel/provider failures, authentication, source correspondence,
full-view privacy and the resource-bounded FS lift remain separate.

In particular, a polynomial image condition for one gamma batch is not
component-wise original-code membership. Noncomputable geometric selection
is not a resource-bounded rewind extractor. No unsupported global error term
is replaced by zero, and no grinding credit is used.

## Reproduction and evidence

Focused command (serialized slot, cached dependencies):

```
bash experiments/run_represented_image_game.sh experiments/represented-image-game-v2.log
```

The runner pins the complete imported source closure to the revision above,
records source/olean hashes before and after the run, uses Lean `-M7000`
with an independent aggregate 7 GiB RSS guard, and records `/usr/bin/time -l`
wall time, peak RSS, swap and the theorem axiom audit. No unchanged dependency
replay or package build is scheduled.

Run from this research directory, using a fresh log filename when reproducing.

The [successful v2 log](experiments/represented-image-game-v2.log) records
exit **0**, **13.15 seconds**, peak RSS **5,624,152,064 bytes**, **0 swaps**,
and unchanged source/cache provenance. Eight audited declarations use only
`propext`, `Classical.choice` and `Quot.sound`; no new axiom or `sorry` occurs
in the retained result. The check used Lean 4.32.0 and cached mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`.

| Artifact | SHA-256 |
|---|---|
| RepresentedImageGame.lean | `71c93cc12d35d6ee3156e0e87872dde7b3b246b6aca58d9737579ba97cc93e5c` |
| RepresentedImageGame.olean | `f6fe69e35e1e46781d1fa78a1fccc2b3fd6aa5b86436af76159141b4ee4e8ef1` |
| Runner | `5e21f443e0f85106b0f4f247bf74ad7757e1fbfa16dc2a6a49d0190fbc485fc6` |

The [retained v1 failure](experiments/represented-image-game-v1.log) was a
single elaborator recursion-depth error while exposing a constructed
`After.difference`, not a failed mathematical implication or memory-pressure
kill. The replacement derives its equality independently with a restricted
constructor simplification before applying the bound. No resource cap was
raised and no unchanged heavy target was replayed.

The [same-word geometric composition](pre-anchor-joint-continuation.md) now
connects this supported event, with the sparse eligible-alpha case charged
and all far finals kept in the residual event. This result and its composition
still do not supply component recovery or payment knowledge.
