# R17 witness-changing semantic and first-relation compensation

Date: 2026-09-21. Source base `1c82c2ad` plus this changeset.
Research-host, fixed-prefix diagnostic; no production change.

## Construction and checks

The prior C1/H1 witness correction now feeds an actual old/new message
pair into the selected payment terminal. The diagnostic uses the literal
28-point interpolation and Boolean-suffix enumeration at all ten rounds,
holding the real execution's prefix fixed. It does not linearize the C1
terminal or reuse an H1 map from the wrong witness context.

It records 271 normalized difference coordinates: the initial difference,
then each round's c0 minus half its incoming difference and c2..c27.
All ten boundaries and the final terminal identity are checked. These
private coordinates remain in-process.

G is solved in its 1022-dimensional OOD-zero quotient space. The 625
equations cancel those 271 semantic coordinates while retaining 88 raw
values, three point values (including the structured-G first point), 256
final values and inactive balance, and cancelling the six compact
first-relation coefficients. The target for the latter is the **combined
C1/H1** residual divided by gamma^27, not the earlier H1-only gamma ratio.

Both actual fixture prefixes have rank 601 and all 24 augmented
compatibility residuals vanish. All original equations are checked.
Independent checks use the selected encoder, OOD and ordinary MLE routines,
structured-G coin evaluation and first-relation polynomial routine. All
seven relation coefficients cancel, including the reconstructed c4.

After applying G to the alternate message vector, the entire ten-round
old/new terminal enumeration is run again and all 271 coordinates are
zero. The source initial-claim builder is also run on the corrected trace
and corrected G; its claim equals the original initial claim.

## Retained v15 failure: initial claim is an affine target

v15 incorrectly asserted that the C1/H1 correction alone left the initial
claim unchanged. World0 exited 101 at this assertion after the C1/H1 checks
passed. The selected initial mask includes witness-column contributions;
the observed semantic initial offset was nonzero. World1 was not run for
that version. The log and staged source are retained.

v16 replaces this false precondition with two stronger source checks:

1. Before G compensation, the semantic initial offset equals the difference
   returned by the actual initial-claim builder.
2. After compensation, the actual initial claim equals the original.

Coordinate zero remains in G's solved target. No initial observation is
dropped, and eta-after-initial chronology is not replaced by a new sampler.
This remains a fixed-prefix calculation, not a justified oracle coupling.

## Exact remaining boundary

The first universal proposition is that the source-derived affine targets
belong to the compatible images for **every eligible witness/mask context
and source prefix outside a quantitatively bounded exceptional set**.
Two successful fixtures do not establish this. The correction must then
be tied to an invertible, measure-preserving transport of the actual coin
distribution; the compiled conditional transport lemmas do not supply the
missing source coverage or seed-expansion premises.

Both channel Final256 differences vanish; later relation arithmetic uses
these same arrays and unchanged weights at a fixed prefix. This gives an
algebraic route to retaining the remaining relation rounds, but no new
universal source refinement of that continuation is claimed here.

Commitment roots/frontiers are not held equal by this diagnostic, and no
complete alternate proof is emitted. Adaptive challenges, the shared hash
oracle, seed expansion, failures, retries/publication, explicit loss bounds
and malicious-prover soundness remain open. Nonhost source pins remain
enforced rather than waived. Existing negative regressions are unchanged.

## Focused evidence

Source revision `1c82c2ad` plus this changeset. The retained cache is
`target/r16-basis-host`; stage manifests specify the exact host manifest,
features and RUSTFLAGS. Builds were offline/locked/release/jobs=1. Runtime
used the honest fixture, selector 0 or 1, `ASPIS_R17_C1_WITNESS_AUDIT=1`
and `NO_DNA=1`; live/complete contexts, oracle/nonce and scan overrides
were unset. Arithmetic work is terminal enumeration and named 625-by-1022
G elimination, not a debug-profile search. All jobs used `/usr/bin/time -l`.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| v15 host build | 0 | 50.21 | 703709184 | 0 |
| v15 world0, false initial-zero precondition | 101 | 14.21 | 287834112 | 0 |
| v16 source-initial-bound host build | 0 | 49.56 | 614105088 | 0 |
| v16 world0 complete diagnostic | 0 | 25.20 | 252329984 | 0 |
| v16 world1 complete diagnostic | 0 | 24.03 | 287621120 | 0 |

No Lean target changed or compiled; no new axioms audit is claimed.
Artifacts under `/tmp/aspis-r15-host.drHYn9`: stages
`r17-two-channel-source-v15`/`v16`, build logs `r17-build-v15.log` and
`r17-build-v16.log`, execution logs `r17-v15-world0.log`,
`r17-v16-world0.log`, `r17-v16-world1.log`.

Stage manifest SHA-256:

- v15: `d305affd01a36ce29bde5b91237f51737806364388560729473ea3dd99b5afa4`
- v16: `15220d13f14f0e919ceb64b480eff6f0e8a59d18559ac97358a1d75fbda757ab`

The original emitted proof hashes remain
`a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5`
and `e81cd45d977e56ce4c5307dc792a468b182dc2d44b2722670aa0a140a38613a7`.
These establish diagnostic transparency only, not equal proof distributions.
