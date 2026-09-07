# Joint image/relation gate: independent review of 67ba3ff1

## Status and scope

Reviewed `DJBarker87/aspisZK` at
`67ba3ff1377bbb788d33e2e4a30b5b8b9bf1f5e9`. This package changes no repository
files or deployed program. It contains a mathematical derivation for a SPECIFIED
ideal image-aware relation verifier plus executable algebra checks. It is not a
kernel-checked Lean theorem, a source-correspondence proof, a whole V8 security
claim, a full-view hiding proof, or a CU benchmark.

The separate V8 implementation commit `07b66afc...` referenced in the report
was not retrievable through the connected GitHub action. Consequently this
review does not claim to establish whether those actual kernels already install
the image functionals at the necessary time. The available research/source
models identify the checks a correct implementation must provide.

The user's accepted body allowance remains 40,282 bytes. This proposal does not
authorise a larger body, changed production acceptance, a push or a deployment.

## What the new obstruction means

The committed base-valued word T_512 is outside
W={A(x)+yB(x): deg A,deg B <=511}. Yet for legal OOD points and the affine
interpolant I and chord L, its virtual quotient Q=(T_512-I)/L lies in W and
folds to a degree-<=255 polynomial F*. A malicious prover is entitled to send
that F* after alpha_0. All pointwise query checks then agree globally.

Thus a bound on the probability of quotient-query acceptance alone cannot
cover every failure of original-code membership. The missing image/relation
check is indispensable. This is neither a payment forgery nor a statement about
the actual scheduler's narrow width29 probability.

## 1. The concrete residual is cheap and nonzero

Write L=a+b*x+c*y. In the y-low-bit natural tensor ordering,

    E1(Q) = Q[1023]
    E2(Q) = b*Q[1022] - c*Q[1021].

Membership in the image of the original-space quotient map is equivalent to
E1=E2=0, given legal distinct OOD points and the exact encoder conventions.
The checked research derivation of these functionals remains a source/Lean
instantiation obligation.

For f=T_512, the quotient has Laurent support [-511,511]. Therefore E1=0.
Let l_+=(b-i*c)/2, l_-=(b+i*c)/2. The Laurent endpoint coefficients satisfy

    l_+*Q_Laurent[511] = 1/2,
    l_-*Q_Laurent[-511] = 1/2.

The leading-coefficient ratios from Chebyshev to the natural tensor are 256:

    Q[1022] = 256*(Q_Laurent[511]+Q_Laurent[-511]),
    Q[1021] = 256*i*(Q_Laurent[511]-Q_Laurent[-511]).

It follows exactly that E2=512. For an occupied component ell and nonzero gamma,

    E1(gamma^ell Q)=0,
    E2(gamma^ell Q)=512*gamma^ell !=0.

This is stronger than merely observing that some unspecified image constraint
fails. It identifies the precise discrepancy to carry into the relation proof.

## 2. Proposed gate and challenge order

Let w,C denote the already fixed ordinary relation covector and claimed scalar
on the quotient, with all interpolant corrections correctly applied. Introduce
a FRESH, domain-separated nonzero image challenge tau after all data determining
Q,w,C is fixed and BEFORE the first degree-six relation response. It is not a
reuse of the old semantic eta. Set

    w_tau = w + tau*e_1023
                  + tau^2*(b*e_1022-c*e_1021),
    claimed scalar remains C.

The two added claims are known to equal zero for a valid original-space
quotient. They need no transmitted claim values. The relation polynomials
still have degree at most six because the protocol proves a linear functional
on the same 1024-vector; changing its coefficients need not increase that degree.
Actual transcript, decoder, proof format, source, ZK and CU obligations remain.

The scalar discrepancy is

    Delta(tau)=C-<w,Q>-tau*E1(Q)-tau^2*E2(Q).

For nonzero image vector (E1,E2), this polynomial is nonzero of degree at most
two regardless of the ordinary prior discrepancy. It has at most two roots
among nonzero tau. For the fixture E1=0 and E2=512*gamma^ell. Do not assume the
ordinary prior discrepancy is zero just to remove this two-root allowance.

## 3. Joint ideal bound allowing the final candidate to be adaptive

This theorem target is restricted to prefixes for which the actual virtual
quotient word is EXACTLY an encoded polynomial Q in W before tau and has
nonzero image vector. It covers the new full-degree example; it deliberately
does NOT cover arbitrary non-polynomial or merely nearby words.

Assume the exact quotient encoder commutes with the arity-four fold. Let
F*=fold_alpha0(Q). The honest reference relation polynomial is the degree-six
primal/dual convolution on Q and w_tau. Its boundary is <w_tau,Q>. The
verifier reconstructs the claimed relation polynomial from its incoming scalar
C, so when Delta!=0 the difference between claimed and reference polynomials
is nonzero and has degree <=6. A fresh alpha_0 makes the discrepancy vanish
with probability at most 6/k.

Outside those initial exceptions, the running scalar differs from the true
folded dot product. Now allow the prover to choose ANY degree-<=255 final
polynomial F depending on tau, alpha_0 and the prior transcript, provided it
is fixed before the query schedule.

Case A: F=F*. All authenticated query values match F. The shifted query
injection cannot remove the nonzero prior discrepancy: its residual vector
is zero, so its constant discrepancy remains. Terminal acceptance requires
a repair in one of the three later degree-six rounds, at total probability
at most 18/k under fresh conditional challenges.

Case B: F!=F*. The nonzero degree-<=255 difference F-F* has at most 255 roots
on distinct final-domain points. Conditional on this complete adaptive prefix,
a fresh uniform distinct q-query schedule has all residuals zero with
probability at most choose(255,q)/choose(T,q). No independence of F and
alpha_0 is required; the target is fixed only at the query boundary.

If at least one residual is nonzero, the Tag-73 discrepancy

    prior - rho*sum_i residual_i*rho^i

is a nonzero degree-<=q polynomial in fresh nonzero rho, for EVERY prior
scalar. It cancels with probability at most q/(k-1). Otherwise later terminal
acceptance again requires one of the same three degree-six repairs. This
18/k allowance is charged once across the partition, not separately per case.

Consequently a conservative ideal conditional bound, for any causal prover
in this exact-polynomial/image-invalid class, is

    Pr[accept] <= 2/(k-1) + 6/k
                + choose(255,q)/choose(T,q) + q/(k-1) + 18/k
              = (q+2)/(k-1) + 24/k + choose(255,q)/choose(T,q).

At k=(2^31-1)^4, q=22, T=262144, the exact expression is less than 2^-118,
with display value 118.4150374966 bits. The different-final query term alone
has display value 221.4682257447 bits.

This is a mathematical derivation of a restricted ideal-game statement. It
is not a claimed error term for the actual provider or a security certificate.
Every freshness, encoding, authentication and discrepancy equation above must
be supplied by the defined game and then connected to the actual source.
The later-round repair proof must allow prover responses to depend on ALL
previous challenges, rather than assuming the whole transcript fixed upfront.

No grinding is credited. No raw fixed-prefix bound is substituted for a ROM
master-tape probability. Hash binding, sampling exhaustion/conditioning,
retries, nonce freedom, replay/FS resources and full-view ZK are not absorbed
into an invented small error. Do not add the displayed 24/k to an existing
ledger that already counts the same four relation collisions without checking
event overlap.

## 4. Compact terminal contribution, not a dense 1024-vector

For actual dual factors [1,alpha^3,alpha^2,alpha]/4, four successive folds
send all three image basis vectors to terminal index 3. The combined image
covector contributes ONLY

    terminal[3] += alpha1*alpha2*alpha3 / 256
                   * (tau*alpha0
                      + tau^2*(b*alpha0^2-c*alpha0^3)).

Indices 0,1,2 receive zero. This follows directly from base-four digits of
1023=(33333)_4, 1022=(33332)_4, 1021=(33331)_4. Existing alpha powers can be
reused; the expression does not require a new live-field inverse.

This is a weight-accumulator update within the SAME relation sumcheck, not a
standalone late image test. For example, on the final input block the vector
(-alpha0^3,0,0,1) folds to zero, but changes E1 by one. Thus final256 alone
does not determine the pre-fold image residual. A check that merely assumes
an image-valid preimage of the final vector is unsound as an original-word link.

No proof-body bytes are algebraically forced by these two zero claims and a
verifier-derived challenge. That does not establish unchanged CU or ZK. New
source work, domain separation and compiled profile bindings are real changes
unless the available implementation already provides the complete gate.

## 5. What remains outside this result

The image-valid, high-J root-product examples remain essential. The zero
candidate satisfies E1=E2=0, while the virtual received quotient need not be
an exact polynomial globally. They are outside the theorem class above.
A global post-gamma quotient codeword must not be assumed for those branches.

The next whole-protocol argument should keep distinct:

- exact-polynomial but image-invalid branches (the restricted joint gate above);
- covered image-valid branches with valid witness/semantic recovery;
- non-polynomial or uncovered image-valid branches, whose accepted mass still
  needs a new query-aware recovery bound;
- authentication, sampling, replay, batching and later-repair exceptions,
  with proper causal source connections and no discarded provider-none mass.

The report's high-J event is a LOWER bound on one intermediate/query subevent,
not a universal error allowance. Rejecting T_512 is necessary, not sufficient
for the 100-bit claim. No new proof-size, memory or performance ranking is
established by this package.

## 6. Executed checks

Run:

    python3 check_joint_image.py --output results-replayed.json

Python 3, standard library only. It tests the existing QM31 tower model, not
compiled production Rust. Exact finite checks include:

- Four coefficientwise T_n chord divisions/reconstructions (n=8 and n=512,
  generic and equal-x OOD pairs), 24 quotient evaluation points.
- 24 exact gamma-scaled top image residuals, testing semantic and mask-only lanes.
- 80 full 1024-entry image-covector/four-fold comparisons with the compact formula,
  all four terminal values, including zero and unit folding challenges.
- 15 relation-convolution boundary/evaluation identities over lengths 4..1024.
- 2640 image-mixing triples and 2662 shifted-batch triples exhaustively checked
  over F5, F7, F13; 96 degree-six discrepancy polynomials over F17.
- 2352 distinct affine-final pairs and 23520 associated two-query schedules.
- Four exact single-fold kernel examples showing why a final-only gate is not
  equivalent to checking image membership of the actual pre-fold quotient.
- Exact rational evaluation of the proposed restricted ideal bound.

These checks do not enumerate all adaptive strategies, prove the universal
bound by testing, or supply an actual source gate. Lean, Rust and SBF tools
are unavailable in this environment; no replay or performance result is claimed.

## Primary source anchors read through the GitHub connector

All repository paths below refer to commit 67ba3ff1 unless noted:

- docs/research/v8-no-work-100-20260907/adaptive-tail-review.md
- docs/research/v8-no-work-100-20260907/experiments/adaptive_outside.rs
- docs/research/v8-no-work-100-20260907/experiments/FullDegreeOutside.lean
- docs/research/v8-no-work-100-20260907/relation-link.md
- AspisFormal/AspisFormal/K1/V7Tag73JointQueryBatchSoundness.lean
- AspisFormal/AspisFormal/Pool/V7RelationCandidateBinding.lean

Mathlib primary root-count reference, consulted 2026-09-07:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Polynomial/Roots.html
The pinned project may use an earlier revision; follow its actual declarations.
