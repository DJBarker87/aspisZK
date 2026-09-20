# R17 structured G candidate: first placement rejected

Date: 2026-09-20. Base revision: `fbf7dbad`.

This is a candidate design and a negative diagnostic, not an implemented
protocol profile. R16 host and production paths remain unchanged.

## Proposed semantic mechanism

Use 271 of the existing 1024 G field coordinates: one initial scalar g and
27 coefficients for each of ten polynomials P_r. The degree-at-most-27
zero-boundary space has basis `1-2X` and `X^k-X` for k=2..27; hence
`P_r(0)+P_r(1)=0`. Define

`R(X) = g/2^10 + sum_{r=0..9} P_r(X_r)/2^(9-r)`.

Its Boolean sum is g. At semantic round r, after prefix z, its suffix sum is
`g/2^(r+1) + sum_{j<r} 2^(j-r) P_j(z_j) + P_r(X_r)`.
Equivalently it is half the previous carry plus P_r. Thus the initial
scalar and each round's 27 independent polynomial coordinates give a
causal triangular coordinate map. This elementary derivation is not yet
a compiled Lean theorem or a refinement of the source sumcheck.

The proposed terminal G claim would evaluate R, replacing the first G MLE
claim and its old multiplicative factor. The other two G MLE claims remain.
This requires changed G functional weights in both prover and verifier,
including inverse-dual transport and batching; honest correctness alone
would not establish malicious-prover soundness. No such changes were made.

## First placement and failed gate

The naive placement uses original G entries 0..270 directly. Test these
271 coordinates jointly with the existing 88 raw observations, two retained
MLE claims, 256 Final256 coefficients and one inactive claim. The new first
G terminal claim is a function of those 271 coordinates, not a free omitted
observation. Two OOD evaluations are held zero via the existing chord/image
parametrization, leaving 1022 input directions.

At the retained R16 fixed challenge/query fixture, the 618-row map has
rank **540**, not the required **596 = 618-22**. There are therefore 56
additional constraints beyond the 22 unavoidable fold relations. This
rejects unrestricted compatible-target coverage for this placement.
It does not prove that every actual witness correction violates a constraint,
that all structured placements fail, or that the original source has an
additional attack. No challenge-probability or adaptive-transcript claim follows.

The shared diagnostic checks every input direction against actual raw/fold
evaluators, eliminates the matrix with invertible row operations, checks its
zero remainder, and independently checks a left inverse on pivot columns.
The failed proposal is retained as
`r17_structured_g_first271_negative_compatible_image`, requiring rank 540.
The R16 positive test still requires rank 408; neither target was weakened
into accepting a smaller positive coverage claim.

Initial failed command: `/usr/bin/time -l cargo test --offline --locked
--release --jobs 1 -p aspis-prover --lib
r17_structured_g_candidate_final256_compatible_image -- --nocapture`.
Exit 101; wall 21.49 s; peak RSS 524681216 bytes; swap 0; compilation 19.33 s;
test 1.69 s. Expected work was focused compilation followed by optimized
QM31 elimination. No Lean source changed; axioms audit is not applicable.

Final regression command used the same options with filter `compatible_image`.
Both tests passed: R16 rank 408, R17 negative rank 540. Exit 0; wall 24.70 s;
peak RSS 523698176 bytes; swap 0; compilation 18.81 s; tests 5.41 s.
The R16 rerun was required because its matrix builder was refactored into
the shared helper; no unchanged full suite or host replay was run.

## Next obligation

Find and justify a fixed public extraction of 271 round-mask coordinates
from existing G coins whose remaining kernel covers the compatible PCS
posterior, or prove that the actual narrower correction targets suffice.
Directly selecting the first 271 entries does not meet the former condition.
A new placement must retain this failure and be justified for the actual
adaptive challenge law, not merely pass another fixed-fixture rank probe.
Only after that should the new functional be source-instantiated. Full
privacy and soundness, including oracle/seed, failures/retries/publication
and explicit losses, remain open.
