# R17 two-channel opening: arithmetic prototype and exact boundary

Date: 2026-09-20. Base revision `79295dc4`, plus the files committed with this
ledger. No production path or staged R16 host was changed. This does not
establish full privacy or malicious-prover soundness.

## What is now implemented and checked

The test-only `crates/aspis-prover/src/r17_two_channel.rs` implements the
ordinary and structured-G functional weights separately. It uses the
literal natural-basis `xt`/chord transpose from the source identified in
`R17_MIXED_MASK_BOUNDARY.md`, after the shared R16 inverse-dual transform.

For the proposed channels `c_R = I_R + L*q_R` and `c_G = I_G + L*q_G`, the
arithmetic test checks both nonzero interpolants, both OOD evaluations,
the original-row claim minus interpolant contributions, and the sum of
the two quotient functionals. It then uses the actual core
`polynomial_for_extension`, `boundary_sum`, `evaluate` and weight-fold
routines through all four relation rounds.

The prototype publishes two 256-coefficient arrays, checks 22 raw/final
equations for each channel with the actual circle/final evaluators, and
injects the two sets using **disjoint** powers rho^1..rho^22 and
rho^23..rho^44. Reusing the same powers for both would allow opposite
channel residuals to cancel identically. The test discards its original
quotient vectors before producing the last three relation rounds: these
use only the proposed public Final512, public weights/openings and later
challenges. This is prototype dataflow, not a replay of new source bytes.

The relation compact convention is explicitly retained: send coefficients
`c0,c1,c2,c3,c5,c6`; reconstruct `c4 = claim/4-c0`. This is different from
the semantic polynomial convention `c0,c2,...,c27`.

The existing shared-functional negative is not removed or reclassified.
The new arithmetic uses two distinct inputs and functionals, precisely
the distinction that the old one-input identity could not represent.

## Formal identities and soundness-loss accounting

`AspisV8R16/BalancedTransport.lean` now proves additivity and supplies
`transportAddEquiv` in addition to its previously proved inverse laws.
`AspisV8R17/TwoChannelOpening.lean` proves the two-functional pullback
identity and instantiates its transform with that actual R16 algebraic
balancing/permutation model. The chord map is an additive-map parameter;
Rust/Lean correspondence, commitment extraction, and Fiat--Shamir soundness
are not silently supplied by the theorem.

`TwoChannelImageGate.lean` proves a finite root-count bound. The proposed
image gate has four residuals:

`q_R[1023]`, `b*q_R[1022]-c*q_R[1021]`,
`q_G[1023]`, `b*q_G[1022]-c*q_G[1021]`.

They are weighted by tau, tau^2, tau^3, tau^4. For the image part alone,
a fixed nonzero residual vector has at most three bad nonzero challenges.
But the complete relation can also have an ordinary-claim error e0, so
the relevant polynomial is `e0 + tau*r0 + ... + tau^4*r3`. Its bound is
**four**, not three, bad nonzero challenges. Similarly, the 44 query
residuals together with the carried-claim error have degree at most 44.
The generic compiled `badCombinedChallenges_card` covers both cases.

For fixed nonzero residual vectors and an independent uniform nonzero
draw from a field of size Q, these give conditional bounds
`4/(Q-1)` and `44/(Q-1)`, respectively. The source must still justify when
the residuals are fixed, the relevant oracle/seed conditioning, sampler
law and query-budget accounting. These are not end-to-end soundness or
privacy bounds and do not replace the rest of either security ledger.

All new/changed formal targets compile with only subsets of `propext`,
`Classical.choice`, `Quot.sound`; no placeholders or new security axioms.

## H1 coverage of the other channel's listed observations

The fixed-challenge test parametrizes the same 1022-dimensional
OOD-zero/chord-image quotient space used in the retained G diagnostic.
It imposes 214 active-row zeros and the inactive-balance equation on
`T^-1(L*q)`. Their rank is 215, leaving 807 directions. All 807 generated
kernel basis vectors pass the **actual** H1 pad application routine.
Thus these are legal changes to the retained pad, not newly sampled H1.

The observation rows are 88 raw values, three original-row MLE point
claims, and a separate Final256: 347 total. The augmented matrix has rank
540, so the restricted observation image has rank `540-215 = 325`.
The 22 fold constraints are checked on every input basis direction and
shown independent through their disjoint nonzero raw blocks. Therefore
this fixture has no further linear obstruction in this listed H1 view.
RREF zero remainders and independent inverse products on original pivot
columns check both rank certificates.

The exact source helper in `state_only_hiding.rs:248-302` has SHA-256
`bc6439203d072cdb3690a290fbadafd828e1c3a2277789bd10f5c2ae6569ec15`,
identical to base `9e432896a4e1515efebe940b71fd9b4f9f009189`. The whole file
differs from that base only by the retained R11/R13 test-module declarations;
this difference was inspected, not waived. The core `sumcheck.rs` is
unchanged from that base, SHA-256
`7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead`.

## G coverage now includes the first relation polynomial

The new `r17_structured_g_first_relation_compatible_image` extends the
618-row mixed-G diagnostic by the six actually sent relation coefficients.
Its weight vector includes the structured-G first point, the two old MLE
points, inactive sum, inverse-dual/chord transport, and the proposed G
image weights tau^3/tau^4. The actual core relation polynomial's boundary
and evaluation at alpha are checked on all 1022 quotient basis directions.

The map has rank **601 of 624**. Besides the 22 raw/fold equations, one
additional equation equates the polynomial's evaluation at alpha with
the weighted Final256. Its coefficient on sent c1 is the checked nonzero
alpha, making it independent of the raw/fold equations. The rank exactly
matches this upper bound; a pivot inverse product supplies the lower check.

This is still a fixed-challenge map. H1's semantic contribution and the
sum of the two channel relation polynomials must be composed with the
retained causal-coordinate and R11 posterior-elimination arguments.
Separate ranks are **not** asserted to be a complete joint H1/G coupling,
and no used observation is discarded to infer uniformity.

## First remaining source obligation

Implement the proposed two-channel relation in a separately staged,
domain-separated research profile, with matching prover and verifier:

1. Replace only the intended G semantic/initial/first-point functionals;
   preserve eta-after-initial, C2 commitment and all other chronology.
2. Bind both deterministic functionals before tau; construct/verify both
   quotient channels and their four image residuals. Preserve component
   OOD claims and nonzero gamma batching.
3. Canonically serialize and absorb **both** Final256 arrays before query
   selection. Authenticate both raw quotient channels from the retained
   C1/C2 openings, then use disjoint query-injection powers.
4. Verify the summed relation polynomial through all four rounds and both
   final channel values. Reject old/new profile confusion and malformed
   framing; do not relax a check to make the fixture pass.

The arithmetic prototype has no new wire parser, actual shared-oracle
execution or complete proof producer/verifier yet. After integration,
establish the joint causal correction for actual C1/H1 witness offsets,
the exceptional-prefix rank/loss bounds under the source law, commitment
and seed-expansion premises, failures, retries and publication. These
remain part of the original full-repair goal, not optional follow-ups.

## Execution evidence

Rust command prefix: `/usr/bin/time -l cargo test --offline --locked
--release --jobs 1 -p aspis-prover --lib`. Expected cost was compilation,
then the named optimized elimination/certificate check or arithmetic test.

| Filter | Exit | Wall seconds | Peak RSS bytes | Swap | Test seconds |
| --- | ---: | ---: | ---: | ---: | ---: |
| `r17_h1_second_channel_final256_compatible_image -- --nocapture` | 0 | 25.14 | 535298048 | 0 | 4.37 |
| `r17_structured_g_first_relation_compatible_image -- --nocapture` | 0 | 29.11 | 534773760 | 0 | 7.74 |
| `r17_two_channel_opening_arithmetic_and_public_tail -- --nocapture` | 0 | 23.12 | 522977280 | 0 | 0.07 |
| `final_posterior:: -- --skip r17_structured_g_first_relation_compatible_image --nocapture` (three retained targets) | 0 | 10.26 | 102907904 | 0 | 10.03 |

The last run checked the changed shared dispatch against retained ranks
408, 540 (negative), and 596; it did not repeat the new first-relation test.
The first H1 draft failed type checking because M31 has no `square` method
(exit 101, wall 2.42 s, RSS 399327232, swap 0); replacing it by the actual
`mul` API fixed the compile error. No failed mathematical target was weakened.

Lean used the cached `/Users/dominic/ZK/AspisFormal` workspace and
`/usr/bin/time -l lake env lean -j1 -M1800 -R <pack>/lean -o <cached-output>
<target>`. Dependent files prepend `target/r17-lean` and, where needed,
`target/r16-lean` to the inherited `LEAN_PATH` using `lake env python3`
before executing Lean with the same arguments.

| Final formal target | Exit | Wall seconds | Peak RSS bytes | Swap |
| --- | ---: | ---: | ---: | ---: |
| R16 `BalancedTransport.lean`, additive extension | 0 | 8.30 | 1333739520 | 0 |
| R17 `TwoChannelOpening.lean`, instantiated bridge | 0 | 8.25 | 1357692928 | 0 |
| R17 `TwoChannelImageGate.lean`, full residual bound | 0 | 10.82 | 1767669760 | 0 |

The generic opening predecessor also compiled (8.03 s, RSS 1262288896),
and the image-only predecessor compiled (6.26 s, RSS 1766211584), both exit
0 and swap 0. Their final reruns were required by the added transport
instantiation and ordinary-error accounting. Every formal result printed
its axioms. No unchanged full suite/manifest, cold build, deployment,
wallet operation or merge ran.
