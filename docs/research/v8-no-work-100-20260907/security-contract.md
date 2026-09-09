# Research security contract — 2026-09-07

Status: no candidate has a complete 100-bit certificate. This directory is
research only; selected acceptance, deployment and payment semantics are unchanged.

Current continuation: [soundness resumed using V7](soundness-resume-review.md).
The optimized research callback now includes the repaired row/image grammar
and compact functional transcript. The historical implementation statements
below refer to their named checkpoints, not to this newer research callback.
New deterministic decoder/payment/compact-round bridges do not fill the
remaining global accepted-extraction or FS bound; the current symbolic ledger
is [here](soundness-resume-ledger.json).

The [joint image/relation game](joint-image-review.md) now has a proved restricted
ideal bound `(q+2)/(k-1)+24/k+choose(255,q)/choose(262144,q)`, 118.4150 bits at
q22. This covers exact polynomial quotients with invalid image under a proposed
fresh-tau gate, not arbitrary oracles or the actual FS execution. Its four
relation repairs must not be double counted in the other inventory. The gate
is not installed in the pinned V8 implementation. No whole-protocol upgrade.

The [query-last audit](adaptive-tail-review.md) separates the prefix-defined
width29 event from query-dependent classifier rejection and from the V8 chord
image/source bridge. In the algebraic chord/query model, absence of an original
component cover can coexist with perfect query agreement; its image residual must be
charged separately. This does not assign H(T)=1 to the actual scheduler or the
narrow width29 event. No new adaptive upper bound or FS certificate is claimed.

New proved subexperiment: [fixed-target query-support theorem](lean-repair-review.md)
uses independent direct q-subsets, nonzero gamma and whole-field alpha. Its
119.0458-bit wrong-support bound is not the adaptive K1.4/extraction error.
General Tag-73 query batching separately costs at most q/(|K|-1) roots with a
fixed prior discrepancy, plus later relation-repair accounting. No FS resource
envelope, provider-none coverage or privacy claim is certified by this lemma.

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

The byte gates are distinct: preferred 30,824; original relaxed 40,000;
user-accepted continuation allowance 40,282; near-miss 40,960.
CU must be <= matched V7 for all four complete transaction shapes on identical
runtime/build conventions, including costly accepted schedules. Host nanoseconds,
base multiplications and the 1.3M limit cannot certify this condition.

The current applicability decision is in decision.md. The 2,800-root scalar
fingerprint theorem bounds only a fixed existing family. A partial provider's
discarded branches require a separate bound. The full-fibre boundary gives a
101.246-bit lower bound on a particular joint same-support recovery event, not
on accepted-proof security. The new 105.142-bit fixed-target folded-query lemma
also is not a full certificate: its pre-challenge target and independent uniform
query hypotheses must be proved for the actual adaptive transcript, then lifted
to the stated FS resource experiment.

The coverage continuation makes the missing term explicit:
`Pr[accept and no valid extraction and not covered]`. A provider returning
`none` does not make this term zero. The <=100 relaxed joint family now covers
all tuples close on >=38,228 symbols, but does not establish that arbitrary
accepted adaptive branches have a batch/fold representation by one of them.
Johnson's lower closeness floor and the query lemma's upper match cap cannot
be substituted for one another. Under the review's conditional inventory,
q23/100 targets leaves ~2^-100.195660 for all omitted soundness/FS terms; it
also exceeds the approved size by 1,245 bytes. Neither is a new security claim.
