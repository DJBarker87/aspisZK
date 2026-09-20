# R17 selected research-host integration

Date: 2026-09-20. Working source: `7a903b432d9e4f549e2f66b59e6b2e895d619347`
plus this changeset. Recovered source base remains
`9e432896a4e1515efebe940b71fd9b4f9f009189`.

This is an implemented, separately staged research profile, **not production,
full privacy, or malicious-prover soundness**. Existing negative regressions
and earlier stages are retained. No new hiding assumption is introduced.

## Implemented correspondence

`tools/stage_r17_two_channel_host.py` first runs the authenticated R16
reconstruction and refuses an existing output directory or an SBF profile.
It records before/after hashes and copies three shared modules verbatim.
The profile is `AV8/R17/structuredG271-two-channel/research-v1`.

- Both commitment trees retain the common R16 transport and existing raw
  records, leaf salts, canonical packed decoder and paired frontier check.
- Existing G coins are mixed once per semantic producer. The initial claim
  replaces the old G Boolean sum by the first mixed coordinate. The first
  G point claim and semantic terminal use the structured mask; the other
  two G point claims and component OOD evaluations remain ordinary source
  evaluations. C2 commitment and eta-after-initial ordering are retained.
- Ordinary and G channels have separate OOD interpolants, inverse-dual/chord
  weights and quotient vectors. The deterministic descriptor and weights
  are absorbed before tau; image residuals use tau through tau^4.
- The wire contains 953 field values, including both Final256 arrays. Both
  arrays are absorbed before query selection and rho. The two sets of 22
  raw/final equations use disjoint rho powers 1..22 and 23..44.
- All four relation rounds are checked. The selected verifier compares
  deferred weights with independent dense folding and unit-basis line
  injection. Raw opening sums also agree with the retained combined-opening
  reference. Shared initial weights are not an independent formal oracle.
- The selected fixture uses zero nonces and no retry/search. It is still a
  deterministic fixture, not an entropy-backed publication adapter.

## Focused evidence

All Rust commands use offline, locked, release, jobs=1. Host compilation
uses the exact flags/features in the stage manifest and the retained
`target/r16-basis-host` cache. Times and peak RSS are `/usr/bin/time -l`;
all rows below reported zero swaps. No Lean source changed: no Lean replay
or new `#print axioms` result is claimed; previous audits remain in
`R17_TWO_CHANNEL_OPENING.md`.

| Target | Exit | Wall seconds | Peak RSS bytes | Result |
| --- | ---: | ---: | ---: | --- |
| `r17_two_channel_opening_arithmetic_and_public_tail` | 0 | 22.33 | 530890752 | 1 passed; shared helper refactor |
| `r17_structured_g_first_relation_compatible_image` | 0 | 9.69 | 81231872 | 1 passed; rank 601/624 |
| initial staged host build | 0 | 47.07 | 736804864 | compiled |
| initial world0 | 101 | 7.48 | 217563136 | retained allocation failure below |
| v2 staged host build | 0 | 48.04 | 714686464 | compiled |
| v2 world0 | 0 | 7.63 | 218218496 | accepted, 43390 bytes |
| v2 world1 | 0 | 7.17 | 218185728 | accepted, 43546 bytes |
| old R16 proof under R17 verifier | 0 | 0.00 | 1835008 | rejected as required |
| v2 recipient-zero control | 143 | 35.94 | 216924160 | intentionally stopped; repeated mixing |
| v3 staged host build | 0 | 47.03 | 641712128 | compiled; negative-fixture cache fix |
| v3 recipient-zero control | 0 | 7.48 | 217251840 | semantic rejection, error 4 |

Both honest worlds pass ten semantic rounds, both quotient image checks,
44 direct raw/final equations, all relation boundary assertions and the
public-byte verifier. Each rejects six byte corruptions, truncation and a
noncanonical G final coefficient; deferred/dense outcomes agree.
These are finite correctness/negative controls, not security theorems.
The invalid recipient-zero witness retains actual C1/C2 commitments and
ten literal terminal-polynomial rounds. Its first boundary is wrong and
the byte verifier rejects at semantic error 4, before PCS; the fixture does
not construct a complete malicious PCS suffix or force future challenges.

Retained failures and fixes:

1. Initial allocation used the old 697 values although the parser required
   953. Ten semantic rounds passed, then parsing rejected with `Length`.
   The generator now allocates `FIXED`; no parser check was relaxed.
2. The negative fixture recomputed the 271-coordinate mixing inside every
   terminal evaluation. It was stopped and changed to reuse the exact same
   fixed mixed vector, as the honest producer already did. The v2/v3 source
   diff is confined to `semantic_negative_fixture`; honest execution and
   verifier sources are unchanged. Therefore honest tests are not repeated.

Local evidence root: `/tmp/aspis-r15-host.drHYn9`. Stages are
`r17-two-channel-source`, `r17-two-channel-source-v2`, and
`r17-two-channel-source-v3`; logs use corresponding `r17-build`,
`r17-build-v2`, `r17-build-v3`, `r17-v2-world0/1` names with `.log`.
These temporary artifacts are supporting evidence, not required preimages
of the checked-in reproducible staging script.

SHA-256 identifiers:

- v2 manifest: `b19e46abd985fda63d504de0ac164759c064017416946bc48cc197fca0d8e458`
- v3 manifest: `a3597a77ea81ad66a431b65253787600c5f8df2397303e140e87967645e6b619`
- world0 proof: `a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5`
- world1 proof: `e81cd45d977e56ce4c5307dc792a468b182dc2d44b2722670aa0a140a38613a7`
- shared public bytes: `9e10f3c9eef4aba72ee047fdf48abdc3ab726a7085ae6381d5a8782bc34e19ad`
- shared transition: `f9474caef25594cf4fffd608428c482485f2764c5cc4da3eafdd5231a5e39766`
- shared binding: `5d8c10fd8d6b2d9846bbb445c7972e10b1c28ae04d97455dd1d239bc9d5afadd`

## First remaining propositions

Subsequent algebra progress is in `R17_SOURCE_ALGEBRA.md`: the reverse
mask loop and arbitrary-input channel residual identities now compile.
Those results do not discharge the concrete source refinement below.

The first source refinement is universal, not another fixture: for every
legal source message vector and challenge prefix, prove that the new
initial/terminal/first-point computations are the compiled structured-cube
model and that `prepare`/`opened` implement the two-functional pullback on
the extracted committed columns. In particular, the G projection must be
the same gamma^27-scaled committed column through component OOD, packed
opening and final checks; the rest is the complementary batch.

For privacy, compose the all-ten-round causal bijection with the **joint**
H1/G posterior preserving all observed point/OOD/raw/final/relation values.
The fixed ranks are not that composition. Establish its exceptional-event
bound at adaptive source challenges, then justify the commitment/shared
oracle/seed expansion and visible failure/retry/publication law.

For soundness, establish coherent extraction and arbitrary-malicious-input
functional correctness, with residuals fixed before their batching draws.
The conditional degree-4 and degree-44 root bounds are not a Fiat--Shamir
security bound. The original three nonhost generated preimages remain
unavailable; this host integration does not waive or reconstruct them.
