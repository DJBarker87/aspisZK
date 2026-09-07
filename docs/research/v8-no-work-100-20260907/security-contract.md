# Research security contract — 2026-09-07

Status: no candidate has a complete 100-bit certificate. This directory is
research only; selected acceptance, deployment and payment semantics are unchanged.

The requested classical claim has two gates, neither of which earns work credit:

1. In the actual interactive experiment, sum every applicable round-by-round
   knowledge error over its adaptive, conditioned prefix. Require the sum to
   be at most 2^-100. Fixed-object query estimates alone are not this sum.
2. In a specified classical programmable/lazy random-oracle experiment, for
   every adversary within a published resource envelope, require
   Pr[accept and extraction fails] <= 2^-100, including authentication,
   extraction, compilation and separately justified primitive terms. Record
   Q adversary calls, all repeated attempts/nonces, R forks, replay calls,
   strict runtime/fuel/restoration limits, and timeout failure. There is no
   resource-independent claim against unlimited offline search.

The application relation must retain owner knowledge, note opening and membership,
statement/attempt/program/release binding, nullifier uniqueness, value conservation,
and atomic pool settlement. Privacy is a separate full-view simulation obligation,
including semantic messages, OOD responses, final disclosure, all authenticated
queries, salts, failed honest searches and aborts. Observed/simulated-proof security
also needs its own simulator programming and freshness/WUR argument.

For selected V7 the proved custom K1.6 compiler has the conditional form

    Pr[accept] <= Pr[valid extracted witness] + e12+e13+e14+e15
                 + (F + choose(F,2) + F*G)/2^256
    M = (R+1)*(Q+1511); F=M+2R; G=Q+1511+R*(2Q+1511).

The four errors must bound the actual proof-relevant operational stage events.
Do not replace them with fixed-prefix probabilities without an adaptive lifting.
The number 1511 is a V7 verifier bound, not automatically a V8 bound. The old
V8 branch's Q=2^36, R=259 is a research envelope, not a resource certificate.
Neither a generic BCS multiplier nor V5 work-normalized arithmetic applies here.
Toolchain/runtime trust is a qualitative boundary, not an invented tiny probability.
SHA/Poseidon concrete assumptions remain symbolic until justified for this game.

Diagnostic erasure removes all three leading-zero checks while retaining nonce
choices, absorbs and every oracle probe. Never divide any error by 2^35, 2^31
or 2^34. In particular, 79 raw bits plus 22 work bits is not 101 requested bits.

For uniform distinct schedules S and an enforced predicate C, a fixed bad set B
has Pr[S subset B | C] <= choose(|B|,q)/#C. A bounded first-valid scan has this
conditional law only with identical independent candidate laws (or a proved
conditional equivalent), symmetric sampler aborts, fixed prior B, and genuine
verifier enforcement. Under those hypotheses success is 1-(1-alpha)^K and
expected candidates attempted is (1-(1-alpha)^K)/alpha. An adversary-selected
outer nonce defeats a one-candidate interpretation; charge its resources separately.
Checking a successful nonce does not establish first success. No query conditioning
cost is a positive security contribution.

For an ideal n-bit digest with H independently exposed outputs, birthday collision
probability is bounded by choose(H,2)/2^n, with additional target-query terms where
the extraction theorem needs them. A 208-bit digest's 104-bit attack-work scale
is not probability 2^-104. No quantum 100-bit claim is made.

The byte gates are distinct: preferred 30,824; relaxed 40,000; near-miss 40,960.
CU must be <= matched V7 for all four complete transaction shapes on identical
runtime/build conventions, including costly accepted schedules. Host nanoseconds,
base multiplications and the 1.3M limit cannot certify this condition.
