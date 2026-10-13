# Actual-field privacy: constructive route and open gates

Root design, 2026-10-13. This is a proof plan with finite experimental
support, not a privacy certificate for the R1 program.

## Why the older experiment cannot simply be reused

R1 samples gamma in E = WideExact, a quadratic extension of K = QM31.
A correction placed in the K-valued D lane alone cannot generally cancel
an arbitrary gamma-weighted semantic lane. The earlier gamma-in-K experiment
therefore did not test the implemented challenge field.

Use both existing K-valued pads G (lane 27) and D (lane 28). Let g=gamma^27,
d=gamma^28, and c=gamma^lane. In the basis 1,e of E/K, define

    det = g0*d1 - g1*d0
    u = (c1*d0-c0*d1)/det
    v = (g1*c0-g0*c1)/det.

Then c+g*u+d*v=0. Since d=gamma*g,
`det = gamma.c1 * Norm(g)`, which is nonzero when gamma is outside K.
The two coordinate identities and determinant expansion are compiled in
`lean/DualPad.lean`. Connecting them to the concrete field's norm and the
mask layout remains necessary. The exceptional gamma-in-K probability is
about 1/|K| under the actual modulo sampler, not zero.

## A sufficient linear construction

Fix public challenges and query positions. Include all individual-lane
observations in a raw linear map: the three multilinear values, Libra,
two circle evaluations, initial queried codeword values, and inactive sum.
The last coordinate is constrained to zero on balanced legal masks.

For each semantic lane difference Delta_c, choose an eligible balanced mask
n_c with the same raw observation vector. This is possible if the eligible
raw map is onto the balanced ambient observation space. Then
r_c = Delta_c-n_c has zero raw observations and is balanced. Add

    n_G = -sum_c u_c*r_c
    n_D = -sum_c v_c*r_c.

These are legal K-valued balanced pad words. Their individual raw observations
are zero. Their contribution to the gamma-batched word is exactly the
contribution of the residual words r_c. Consequently the correction reproduces
not just selected PCS outputs but the entire batched word. It therefore also
reproduces both R1 folding rounds, intermediate committed word and final
message under any fixed linear PCS observation map.

After this correction, the remaining normalized semantic-round difference
has zero initial and terminal values and lies in the chain subspace Chain0.
If the pure masks with zero raw observations span Chain0, they repair that
remaining difference without changing other observations. The existing
`R0Z/Chain.lean` proves a remainder-membership statement for its R0 model;
its exact applicability to the R1 source payload must be established.

This construction is universal *conditional on the stated linear-map
properties and payload identities*. It does not replace those properties
with a rank observed on one example.

## Efficient simulation, beyond witness independence

A translation between two witnesses proves equality of their conditional
view laws. An efficient zero-knowledge simulator needs more. The existing
R0 formal simulator selects a witness with `Classical.choose`; that alone
is not an efficient algorithm given only the public statement.

A stronger sufficient target is to place the normalized honest offset itself
in the image of a publicly computable mask map, using the same construction
against a zero offset after subtracting known public affine coordinates.
The simulator can then sample independent uniform legal masks, apply that
public linear map, and invert the public normalization. It does not solve
for a witness. For the nonlinear eligible-noise remainder, use the existing
independent-uniform absorption argument after proving its Chain0 membership
and the pure-mask image inclusion for R1. This stronger target has not yet
been source-instantiated or proved.

## Evidence on the actual R1 proof

The proof-driven gate parses and verifies the semantic prefix, derives the
actual gamma, semantic challenges, circle points and 22 queries, and uses
D18 transport. On the recorded Pool transfer proof it obtains:

- all 16 eligible C1 raw ranks: 112;
- balanced H1-padding raw rank: 94 in ambient dimension 95;
- pure compensated round image: 1080;
- its initial-zero part: 1076, the expected Chain0 dimension.

It rejects gamma in K, semantic alpha_i in {0,1}, and alpha_9=1/2 before the
rank computation. Two additional full-field challenge experiments each pass
five witness-difference checks. These are finite checks, not a good-challenge
density theorem or an R1 zero-knowledge theorem. The proof-driven gate takes
about 16.5 seconds including compilation in its recorded optimized NUC run.
Evidence and exact input/source hashes are in `evidence/privacy-wide/`.

## Optional honest-prover rank rejection

A local, fail-closed rank test before any publication could ensure that no
accepted proof is published with a deficient checked map. It would leave
soundness and verifier work unchanged. However it is not a complete shortcut:

1. The matrix must cover the exact full disclosed R1 payload and legal tape.
2. An accepted-transcript simulator and an abort/retry-aware ROM reduction
   must be supplied, including public retry/timing behavior as appropriate.
3. Success density or an explicit bounded-abort contract is needed for
   completeness and practical proving time.
4. Every attempt needs fresh private entropy and durable nonce reservation;
   rejected attempts must not be uploaded or reused.
5. Commitment hiding and oracle-programming failure probabilities still need
   explicit bounds. A rank test alone does not make hash commitments hiding.

The cost harness retains an explicitly insecure deterministic fixture mode.
The default-off salted P3 path now also integrates OS-generated
`StateOnlyAttemptSecrets` with durable nonce reservation. Fresh full-mask
proofs have passed the native and actual Pool paths. The existing rank gate
also passes on one such P3 proof using its actual transcript challenges:
see `evidence/privacy-wide/proof-rank-gate-p3/`. Neither the publication rank
guard nor the efficient simulator and abort-aware ROM proof is complete;
the fresh entropy API does not make this a released private-spend protocol.

The methodological warning about accepted and aborted transcripts is also
consistent with [A Detailed Analysis of Fiat-Shamir with Aborts](https://eprint.iacr.org/2023/245.pdf).
That paper is not an instantiation proof for Aspis.
