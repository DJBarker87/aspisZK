# Actual-source H1 semantic-coordinate construction

Date: 2026-09-20. Base `b6c8b021f1668d5348c59ae883e086a0cae8805b`
plus this changeset. The implementation is an opt-in diagnostic in the
isolated research host, not a production change or full privacy proof.

## Construction

`tools/r17_h1_semantic_audit.rs` is included in the staged payment module
and runs only with `ASPIS_R17_H1_SEMANTIC_AUDIT` set. It consumes the actual
messages and completed semantic challenge vector of that prover execution.
It makes no oracle calls, changes no masks, and does not serialize its map.

At each of the producer's 28 interpolation samples and Boolean suffix
assignments, it calls the **selected source payment terminal**, including
the pair-forest mu^2 inactive-helper term, R17 G substitution and retained
positive-transfer correction. Replacing the first H1 point claim by 0 and
1 extracts its affine coefficient; the value at 2 checks the affine
identity at every sampled point. The source-shaped universal algebra is
separately recorded in `R17_JOINT_COMPOSITION_BOUNDARY.md`.

Sparse MLE weights expand each coefficient onto the 1024 original H1 rows:
the Boolean suffix fixes row suffix bits, so a sample touches only the
prefix rows and the two current-bit choices. This avoids a large dense
expansion at each sample. The same `interpolate_degree27` function as the
semantic producer constructs each of the ten row-wise polynomial maps.

The output is a 271-by-1024 linear-coordinate matrix: the initial Boolean
sum, then the constant coefficient minus half the preceding carry and
the 26 coefficients of degrees 2..27 for each round. Thus it uses the
normalization in the compiled structured-mask recurrence, not merely the
serialized polynomial coefficients relabeled as independent coins.

For each of the 1024 basis directions the diagnostic checks:

- all ten semantic boundary identities against the carried value;
- the final carried value equals the actual source terminal H1 coefficient
  times that row's MLE basis evaluation at the final semantic point;
- `structured_g::mask_eval` on its 271 normalized coordinates equals that
  same terminal value.

It then constructs every balanced inactive-row basis pad (809 directions),
passes it through the actual H1 pad application function, and checks that
its initial contribution is zero. Unrestricted row basis directions need
not have zero initial contribution; that fact was not incorrectly assumed.

## Exact evidence and transcript preservation

Both actual witness contexts pass all checks. Their complete proofs still
pass the selected public-byte verifier, dense/deferred differential and
retained mutation/canonical/truncation controls. The proof hashes are
identical to the pre-audit proofs:

- world0, 43390 bytes:
  `a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5`;
- world1, 43546 bytes:
  `e81cd45d977e56ce4c5307dc792a468b182dc2d44b2722670aa0a140a38613a7`.

This establishes diagnostic transparency for the two executions, not a
general noninterference theorem. Internal matrix entries depend on the
hidden C1 context and are deliberately **not** emitted as public evidence.
Only aggregate assertion results and the already-public proof are written.

Stage: `/tmp/aspis-r15-host.drHYn9/r17-two-channel-source-v6`.
Manifest SHA-256:
`c54e26aa1e70efad62a2ece3e113355ab6ca9eec35ffab3e4024717d5c9af4d6`.
Diagnostic module SHA-256:
`78e8ec35fef9869d4402bef65d28ef834f1dd3aa0abe82ebd1f00e36da9aa91a`.
All reconstruction/source pins remain enforced; unavailable nonhost
preimages are not waived. The staging script hashes the new included file.

## Resource record

Build: offline/locked/release/jobs=1, exact flags/features in the stage
manifest, retained `target/r16-basis-host` cache. Runtime: honest fixture,
`ASPIS_R16_SELECTED_SECOND=0/1`, diagnostic flag enabled, no live context,
oracle-table override, nonce override, frontier search or wallet operation.
The normal ten-round source producer and the new diagnostic are both run.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| v6 staged host build | 0 | 47.05 | 737067008 | 0 |
| v6 world0 with source H1 map | 0 | 10.80 | 223150080 | 0 |
| v6 world1 with source H1 map | 0 | 10.44 | 223215616 | 0 |

Timed logs are `r17-build-v6.log`, `r17-v6-world0.log` and
`r17-v6-world1.log` under the same temporary evidence root. No Lean source
changed; no new compilation or axioms result is claimed. No unrelated
regressions were rerun.

## Remaining proposition

The source H1 semantic-coordinate map and its terminal consistency are
now constructed and checked in two real contexts. Next, combine this map
with the H1 quotient/compact-relation contribution and the G compatible
image to construct the context-dependent correction from `ContextShear`.
It must retain all existing point/OOD/raw/final observations, the serialized
first G point, and the shared relation polynomial, not just semantic values.

These finite checks do not supply a universal Rust refinement, equality
across arbitrary hidden contexts, or an adaptive exceptional-event bound.
The full commitment/shared-oracle/seed, failure/retry/publication and
soundness obligations remain open. The 0/1/2 affine controls are executable
checks; they do not replace the source algebra or its eventual refinement.
