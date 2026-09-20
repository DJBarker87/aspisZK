# R17 affine H1 witness correction: joint retained observations

Date: 2026-09-21. Source base `a41b71183bf5cf8522596fad32f48efb295742ca`
plus this changeset. Research-host diagnostic only.

The same-public opposite-witness construction now goes beyond C1 and the
two helper OOD values. Let dC be its 16 corrected C1 column differences,
and h0 the rebuilt helper difference after the legal OOD-cancelling pad.
The ordinary-channel difference is

`rest = sum(c=0..15, gamma^c * dC[c]) + gamma^26 * h0`.

The other ten C1 columns, G and D have not changed. Both OOD evaluations
of rest vanish. The selected encoder and cached source decoder reconstruct
its quotient qRest. Checks enforce both quotient image conditions and the
full coefficient equality `L*qRest = T(rest)`, not just sampled agreement.

An additional OOD-zero H1 pad is parametrized by the existing 1022 free
quotient coordinates. Its 562 equations retain the 214 active rows and
inactive balance, cancel 88 raw and three point values of h0, and set its
256 folded quotient values to `-Final(qRest)/gamma^26`. The rank is 540 in
both retained fixture prefixes; all 22 augmented compatibility residuals
vanish. Every original equation is checked against the constructed vector.

The pad is checked by the actual source H1 padding routine. The resulting
helper difference is checked with the selected encoder at all 88 raw
locations and source OOD evaluation at both points. v14 additionally checks
the three claims through the actual multilinear evaluator and checks the
**sum of both pads** through the actual padding routine. All 256 folded
values of `qRest + gamma^26*qPad` vanish.

This constructs an affine witness-offset correction, not merely a kernel
direction. No internal correction is exported or installed in the emitted
proof. No production paths, transcript sampling or hiding assumptions change.

## Remaining proposition

Update: `R17_G_WITNESS_JOINT.md` records the following affine G construction
passing at both fixture prefixes, including actual initial-claim checks.
The universal source/distributional boundary remains open.

Compute the complete old/new non-G semantic-coordinate difference using
the corrected C1 and H1 in their respective hidden contexts. Construct G's
correction that cancels this difference and the combined first-relation
polynomial while retaining G's raw/point/OOD/final/inactive observations.
The earlier within-context zero-target example does not prove this affine
compatibility. In particular, retain the serialized structured-G first
point and the actual initial claim in the target.

Even a successful fixed-prefix construction will not prove that commitments
or shared-oracle challenges are unchanged. A causal distributional argument,
source seed expansion, exceptional-event bounds, visible failures/retries/
publication and adversarial soundness remain separate open requirements.

## Exact focused evidence

All jobs used the retained `target/r16-basis-host` cache. Builds used
`cargo build --offline --locked --release --jobs 1`, with manifest and
RUSTFLAGS/features from each stage's `r16-stage.json`. Runtime selected
`ASPIS_V8_POSITIVE_CASE=honest`, `ASPIS_R17_C1_WITNESS_AUDIT=1`, `NO_DNA=1`
and `ASPIS_R16_SELECTED_SECOND=0` or `1`, with live/complete contexts,
oracle-table/final-nonce overrides and frontier-scan override unset.
Time/RSS/swap came from `/usr/bin/time -l`. No Lean files were changed or
compiled; no new `#print axioms` result is claimed.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| v13 joint host build | 0 | 49.19 | 627392512 | 0 |
| v13 world0 | 0 | 9.25 | 287981568 | 0 |
| v13 world1 | 0 | 8.81 | 287965184 | 0 |
| v14 additional source-check build | 0 | 50.21 | 565706752 | 0 |
| v14 world0 | 0 | 9.18 | 287817728 | 0 |
| v14 world1 | 0 | 8.90 | 287899648 | 0 |

Artifacts under `/tmp/aspis-r15-host.drHYn9`: stages
`r17-two-channel-source-v13` and `r17-two-channel-source-v14`; logs
`r17-build-v13.log`, `r17-build-v14.log`, and
`r17-v{13,14}-world{0,1}.log`. Stage manifest SHA-256 values:

- v13: `f9c860b4645ae179a8ce4f82ed59f18d241447d95d16097bf912949610b2cf71`
- v14: `7f4b0273d0c08df74a9624c144199775c3251ee361efd1fd9ee5c0ce339f7a63`

The v14 emitted original proofs retain hashes
`a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5`
and `e81cd45d977e56ce4c5307dc792a468b182dc2d44b2722670aa0a140a38613a7`.
This is diagnostic transparency, not equal transcript distributions.
Source pins and negative regressions remain intact; unavailable nonhost
preimages remain unavailable and are not waived by these host results.
