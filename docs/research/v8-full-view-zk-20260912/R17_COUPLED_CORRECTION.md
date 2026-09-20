# R17 explicit coupled correction, fixed-prefix boundary

Date: 2026-09-20. Base `66afc35a7a254bf600fcc5eacf750229889e0ff1`
plus this changeset. Research-host diagnostic only; no production change.

## Construction and scope

`tools/r17_coupled_audit.rs` uses the in-process, actual-source H1 semantic
map from the preceding milestone. It constructs one nonzero H1 pad change
in the kernel of the retained H1 view, then solves for a G compensation.
All vectors stay internal. Neither vector is installed in the original
proof, and neither is serialized or published.

The H1 system has 1022 OOD-zero quotient coordinates and 562 constraints:
214 active-row zeros, inactive balance, 88 raw values, three original-row
point values and 256 final coefficients. Elimination finds rank 540 and
chooses the first free-coordinate kernel direction deterministically.
The result is checked against every original matrix row and the actual
H1 pad application routine. Its normalized semantic-coordinate effect is
required to be nonzero, with zero initial coordinate.

The G system has 625 observations: 271 mixed coordinates, 88 raw values,
three points including the structured first point, 256 final coefficients,
inactive balance and six sent relation coefficients. Its target is the
negative of H1's semantic contribution, zeros for all retained G views,
and the negative H1 relation contribution with the correct gamma ratio.
Specifically, H1's column weight is gamma^26 and G's is gamma^27, so the
unscaled G relation target is `-gamma^-1 * H1_relation`. Omitting that
ratio would check a different protocol.

The augmented G system has rank 601 and zero residual right-hand sides.
The recovered solution is checked against **all 625 original rows**, not
just the reduced system. Independent Horner mixing of the recovered G
message cancels all 271 H1 coordinates. Calling the actual core relation
polynomial routine checks cancellation of all seven coefficients, including
the omitted coefficient, after their gamma^26/gamma^27 scaling.

The final audit also encodes each recovered delta with the selected host
C2 encoder and checks all 88 queried values are zero. It uses the selected
source OOD evaluator at both OOD points for each delta, the source MLE
evaluator for H1's three and G's two ordinary points, and `mask_eval` for
G's structured first point. This independently checks the diagnostic's
raw/natural-basis and point formulas on the actual correction vectors.

## What this does not establish

This is a **within-context invisible-mask correction**, not a witness
change. It does not cover the R7 nonlinear incidence offset, arbitrary
affine target offsets, or every H1 direction. The source-prefix challenges
are fixed for the calculation. C2 commitment roots would generally change
if the correction were installed; the audit does not claim otherwise or
force the real oracle to return unchanged challenges.

Later relation rounds are not independently reconstructed for corrected
masks in this diagnostic. Their public-tail determinism is retained prior
evidence, not newly established by this run. The first relation polynomial,
raw/opened values and both final arrays are the explicit preserved boundary.
No full privacy, adaptive loss, or malicious-prover soundness claim follows.

## Execution and resource record

The optional `ASPIS_R17_COUPLED_AUDIT` flag constructs the source H1 map
and then performs the two eliminations after the actual query schedule is
known. It makes no extra oracle calls. Normal proof construction and all
existing verifier controls continue afterward. Rust uses the pinned host
flags/features, offline/locked/release/jobs=1 and the retained build cache.
The arithmetic phase is explicitly the H1 kernel and G augmented-system
eliminations, not a schedule or nonce search.

The initial v7 host built and its world0 correction passed. The v8 addition
of direct source checks failed to compile because a local vector named
`ood` shadowed the source function. Qualifying `super::ood` fixes the call;
no arithmetic or acceptance check was relaxed. Failed stage/log retained.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| v7 host build | 0 | 47.85 | 738131968 | 0 |
| v7 world0 matrix/core correction | 0 | 11.97 | 278282240 | 0 |
| v8 host build, name collision | 101 | 40.07 | 676691968 | 0 |
| v9 corrected host build | 0 | 48.81 | 619610112 | 0 |
| v9 world0, including selected encoder/OOD checks | 0 | 12.27 | 295206912 | 0 |
| v9 world1, including selected encoder/OOD checks | 0 | 11.87 | 294928384 | 0 |

Both contexts pass the coupled correction and the ordinary public-byte
proof verifier, with dense/deferred agreement and retained rejection
controls. The published fixture proofs remain byte-identical to the
pre-audit proofs: world0 SHA-256
`a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5`,
world1 `e81cd45d977e56ce4c5307dc792a468b182dc2d44b2722670aa0a140a38613a7`.

Evidence root: `/tmp/aspis-r15-host.drHYn9`. Build logs are
`r17-build-v7/v8/v9.log`; run logs are `r17-v7-world0.log` and
`r17-v9-world0/1.log`. Stages and output directories are retained separately.
Final v9 manifest SHA-256:
`f900b3f51bb09c319de9e1f136a27f2d019e3d7651147c61de3f50ac07040c79`.
Shared coupled-audit module SHA-256:
`561facdd0072f7995c977b5567f19d1a9c361e1674f8eccfb0edd41758a95985`.
All reconstruction pins remain enforced; the three unavailable nonhost
preimages are not waived by these research-host results.

No Lean source changed; no new axioms audit is claimed. Earlier compiled
conditional counting/shear results remain conditional on their stated
source premises.

## Next obligation

Extend this explicit construction to the required affine witness/context
offset, retaining the C1 incidence correction and every listed observation.
Then instantiate the context-dependent posterior bijection, rather than
inferring it from this one invisible direction. The universal/adaptive
exceptional-event bound and commitment/shared-oracle/seed/failure/retry/
publication laws remain separate required proof gates.
