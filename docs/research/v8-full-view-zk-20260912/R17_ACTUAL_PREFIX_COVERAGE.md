# R17 compatible image at actual verifier prefixes

Date: 2026-09-20. Base `9a1db9947b6312cc7284b7d949f34be583af0b04`
plus this changeset. This is executable source-prefix evidence, not a
universal rank theorem, joint simulator, or adaptive probability bound.

## What changed

The staged host has a read-only `--audit-existing DIR` mode. It verifies
the retained `proof-1.bin` against its public/transition/binding bytes and
reports one public-prefix record after successful deferred verification;
the dense verification still runs and must agree. It performs no extra
oracle sampling and outputs no witness, mask or seed.

The fields, in canonical 16-byte QM31 encoding, are ten semantic challenges,
kappa, tau, the first relation-fold alpha, p0.x, p0.y, p1.x, p1.y and gamma.
The record also contains the 22 actual query indices. The fixed-fixture
matrix routine now accepts this prefix explicitly; its previous synthetic
regressions remain. The new test requires a single accepted audit record,
canonical fields, circle equations, distinct points/queries and nonzero
source gamma/kappa/tau. This validates the diagnostic input shape; the
log itself is not a cryptographic authentication mechanism.

Both previously accepted, same-public-input R17 proofs pass the actual
prefix test: the G map has rank **601 of 624**, with exactly the 22 raw/fold
equations and one first-relation evaluation equation. The matrix still
checks OOD-zero/image constraints and source core boundary/fold identities
on every input basis direction, plus an independent original-pivot inverse
product and zero RREF remainder. No proof was regenerated for this result.

Gamma^27 is nonzero. The diagnostic parametrizes the unscaled G quotient;
scaling its final/relation rows by this nonzero scalar gives the G channel's
normalization and does not change rank. This does not identify the G-only
relation polynomial with the **sum** of both channels' wire polynomials.
That joint composition remains an obligation.

Two unnecessary diagnostic exclusions were removed: the image-space basis
requires only that the chord's x/y coefficients are not both zero, and
independence of the first-relation constraint uses c1 when alpha is nonzero
or c0 when alpha is zero. These changes do not assert full rank at all such
prefixes; the rank is still measured only for the listed executions.

## Reproducible inputs and provenance

Retained public-only records:

- `evidence/r17-world0-public-prefix.log`, SHA-256
  `a7f3bae6ac64d17ad5c0bc600988f6a9dc2c5e397cc0ad22f59b21b8dace81d0`.
- `evidence/r17-world1-public-prefix.log`, SHA-256
  `ceb263b0718ca46b5fc3a1786c0298ae9883d4e548b2e512ee7e7de76ace0148`.

They are the first two lines of the successful timed host audits, not the
failed stale-binary runs below. The retained proof hashes remain
`a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5`
and `e81cd45d977e56ce4c5307dc792a468b182dc2d44b2722670aa0a140a38613a7`.

The final stage is `/tmp/aspis-r15-host.drHYn9/r17-two-channel-source-v5`;
its manifest SHA-256 is
`dffa152b8963576c3e6567af7f94cfa318a84d3f29c36ee3a77d7e268d30e9b0`.
Its shared host-relation SHA-256 is
`7464ff262cf5f7472b496f30b33f9e9a4772de88bc2b7dc45490cab4e49f9fda`.
Source reconstruction pins and the three unavailable nonhost preimages
are unchanged and not waived.

Re-run one matrix with:

```sh
ASPIS_R17_PUBLIC_PREFIX_LOG="$PWD/docs/research/v8-full-view-zk-20260912/evidence/r17-world0-public-prefix.log" \
  cargo test --offline --locked --release --jobs 1 -p aspis-prover --lib \
  r17_actual_source_prefix_compatible_image -- --ignored --nocapture
```

## Resource and failure ledger

All compilation/arithmetic used the retained cache, release and jobs=1;
`/usr/bin/time -l` supplied metrics. Every listed run reports zero swaps.
No Lean source changed or new axioms result is claimed.

| Target | Exit | Wall seconds | Peak RSS bytes |
| --- | ---: | ---: | ---: |
| synthetic first-relation regression after parameter refactor | 0 | 31.64 | 560594944 |
| v4 host build, format-string typo | 101 | 41.81 | 736919552 |
| v5 corrected host build | 0 | 47.36 | 717717504 |
| accepted world0 public-prefix audit | 0 | 0.42 | 2785280 |
| accepted world1 public-prefix audit | 0 | 0.02 | 2736128 |
| actual world0 compatible image | 0 | 30.27 | 560021504 |
| actual world1 compatible image | 0 | 8.35 | 81100800 |

The v4 format-string build failed. An incorrectly sequenced audit command
then ran the old v3 binary, which treated `--audit-existing` as a new output
directory and produced a local fixture; the next old-binary invocation
rejected the existing directory. These runs are **not audit evidence**.
Their logs are retained as `r17-public-prefix-world0/1.log`; the unintended
fixture was moved intact to `r17-stale-audit-artifact` under the same temp
root. No user data was deleted. Only after confirming the corrected build's
exit 0 were the successful `r17-v5-public-prefix-world0/1.log` audits run.

## First remaining privacy proposition

At fixed challenges the shared first-relation polynomial couples H1 and G.
Prove a compatible-image composition preserving the earlier semantic
coordinates and both channels' point/OOD/raw/final values, not simply add
the two separately measured ranks. Then prove sufficient coverage outside
an explicitly bounded exceptional set for the **adaptive source** prefix.
A nonzero minor at one or two prefixes does not supply that bound: the
query schedule is sampled from the finite circle domain after Final512,
and the semantic/PCS challenges depend on the prior transcript.

Exact Rust/field refinement, source commitments/shared oracle/seed expansion,
visible failures/retries/publication, and malicious-prover soundness also
remain open. This diagnostic neither restarts schedule search nor claims
full privacy from fixed-prefix linear coverage.
