# Collecting support without assuming accepted queries stay uniform

Research base: `532ade2064e533602902fc9ae5b4dd90f9207131`. This is a
mathematical collector analysis and source-obligation map. It adds no verifier
check, proof value, accepted-extraction bound or Fiat–Shamir theorem. No build
was run for this document. The exact tiny-policy controls are recorded in
[`censored-collector.json`](censored-collector.json); their source is
[`censored_collector.py`](experiments/censored_collector.py).

The useful new reduction is narrow: **the joint event of obtaining 235
qualifying q22 continuations of one frozen final yet at most 255 distinct
matching fibres admits an explicit N-dependent bound despite acceptance
censorship.** It does not produce those 235 continuations, and separately
collected supports need not overlap across finals.

## Exact adaptive collector experiment

Let D be the actual final-index domain, with `|D| = T`. Fix `1 ≤ q ≤ c < T`.
Run at most N query trials. Immediately before trial t's fresh schedule:

- The complete replay history and current retained union U_t are fixed.
- The conditional schedule law is uniform on ordered injections `Fin q ↪ D`.
  Equivalently its underlying q-subset is uniform, but retain the order for
  the source rho batch. This is a conditional law, not marginal uniformity.
- For the one-final interpretation, the received oracle, alpha and final
  coefficients are fixed at the same query boundary throughout these trials.

After seeing the schedule and later transcript, an arbitrary causal filter
may retain or discard the trial. Let J_t record retention. It may depend on
the schedule, rho, later responses/challenges, acceptance, parser outcomes and
aborts. On retention the collector adds **all q indices**:

`U_(t+1) = U_t ∪ S_t` if J_t, and `U_(t+1) = U_t` otherwise; initially U_0 is
empty. Retaining an arbitrary smaller subset is a different collector and
does not have the q-point first-step guarantee below. The filter must be
resolved before the next trial; retrospective editing of old retention flags
is not this online process. An early stop can be padded by discarded trials.

To make U_t a checked matching support rather than a set of observed indices,
retention additionally requires canonical root-bound records from the same
committed words and explicit checks of every pointwise residual. A zero
denominator is rejected, not declared a match. For the relation certificate,
also check the actual carried prior is zero. These requirements only restrict
retention; they do not require its independence from the fresh schedule.
They are **not** inferred solely from scalar verifier acceptance.

## Censoring-safe growth bound

Define a bounded stall at trial t by

`C_t := J_t AND |U_t| ≤ c AND S_t ⊆ U_t`.

Before the schedule, U_t is known. Thus, for every full history,

`Pr[C_t | history] ≤ choose(c,q) / choose(T,q) =: b_c`.

Indeed C_t is a subset of the event that the fresh schedule is contained in
U_t. Its exact probability is `choose(|U_t|,q)/choose(T,q)` when `|U_t| ≤ c`.
Later acceptance/abort censorship can only remove outcomes from this event.
This uses the already available ordered-schedule counting law; it never
treats the conditional distribution given retention as uniform.

Now suppose the final union has at most c points. The first retained schedule
adds q points. Each retained nonstall after it adds at least one. Therefore
at most `c-q+1` retained schedules can be nonstalls. In particular,

`Pr[retained count ≥ c-q+2 AND |U_N| ≤ c] ≤ min(1, N*b_c)`.

For q22 and c255, the threshold is **235**, not 256:

`Pr[at least 235 qualifying continuations AND |U_N| ≤ 255]`
`  ≤ min(1, N * choose(255,22)/choose(262144,22))`.

The one-trial factor is approximately `2^-221.4682`. The deterministic
threshold is sharp: start with a fixed 22-set, then add one new point per
retained schedule while reusing 21 old points. Exactly 234 nonstall successes
can finish with exactly 255 points. A conservative target of 257 fibres uses
c256 and a threshold of 236 instead; the current final-code uniqueness
theorems need only 256.

A stronger witnessed-success-count version is also immediate. For
`r > c-q+1`, set `h = r-(c-q+1)`. The target event requires at least h bounded
stalls. For each fixed h-tuple of trial times, iterated conditioning bounds
their joint stall probability by `b_c^h`; earlier stall events are measurable
before every subsequent draw. A union over the time tuples gives

`Pr[retained count ≥ r AND |U_N| ≤ c] ≤ min(1, choose(N,h)*b_c^h)`.

No independence of the retained trials is used. At q22/c255, `h=r-234`;
256 retained trials with a union still at most 255 would require 22 stalls.
These are unconditional **joint-event** bounds. Conditioning on reaching the
specified number of successes would require dividing by the probability of
that event; the same number cannot silently be reused as a conditional bound.
For example, a policy may retain only schedules inside one fixed 255-set.
Conditional on obtaining 235 retained trials, the union is then at most 255
with probability one; the event of obtaining those trials is itself rare.

The probability argument here is a mathematical derivation, not a
kernel-checked probability experiment. The separate
[`CensoredCollectorGrowth.lean`](experiments/CensoredCollectorGrowth.lean)
is now kernel-checked for the deterministic recursive-union/growth implication,
including the actual earlier-prefix witness at q22/cap255/235 successes. Its
[focused evidence](censored-collector-growth-review.md) records the replay and
six standard-only axiom audits. It does not supply the fresh sampling, replay
or retention probability law.
The exact backward-induction control covers 108 tiny games and 36,822 states,
maximizing over every causal retain/discard choice in those games. This tests
censorship explicitly; it is not a QM31 experiment or a replay extractor.

## What this removes from the replay obligation

For a capped collector, insufficient support splits into two visible cases:

1. Fewer than 235 qualifying continuations were obtained within N trials.
2. At least 235 were obtained, but they still expose at most 255 points.

Under the stated conditional law, the second case has the displayed small
joint bound. The first remains unbounded here. This is a non-circular reduction
from “obtain enough useful successes **and** prove their diversity” to
“obtain enough useful successes,” plus a separately bounded diversity failure.
It does not assert a lower success probability from a witnessed success count.

A single accepted proof is not a lower bound on repeat success at its frozen
prefix. An expected relation-compatible moment is also not a guarantee that
the prover supplies openings or correct later responses there. To derive a
binomial/runtime bound, one would need a justified qualifying-success rate
and the appropriate restored-state conditional law. No such rate is assumed
in this report. Aborts, response omissions, fuel exhaustion, duplicate
challenges, changed prefixes and oracle-state mismatches consume the declared
caps and remain part of the unsuccessful-collection event.

The current suffix theorem separately accounts for scalar acceptance with
nonzero prior or nonzero pointwise residual via the shifted degree-q rho
test and three later degree-six repairs. If those events are used to turn
ordinary acceptance into qualifying acceptance across forks, their challenge
and call accounting must be composed once over those forks. The present
support-growth proof does not charge them again or assume they never occur.

## One-final support is not cross-final coherence

Let M_j be the matching set of an alpha-dependent final F_j. Even if every
collector obtains 256 points of M_j, there need not be any common point across
the M_j. Accepted queries may be entirely concentrated inside each different
M_j. As a scale diagnostic, `(M/T)^22 ≈ 2^-100` corresponds to a matching
fraction around 0.043; four sets that large can be pairwise disjoint. This is
not an exact finite-parameter acceptance threshold, and an averaged moment
does not give such a lower size bound at every prefix.

High-agreement recovery is already handled by
[`PreImageAnchor.lean`](experiments/PreImageAnchor.lean),
[`PreImageAnchorSelected.lean`](experiments/PreImageAnchorSelected.lean) and
[`PreAnchorJoint.lean`](experiments/PreAnchorJoint.lean): under
`5*B+255<T`, either at most three alpha values permit a B-close final, or one
pre-tau geometric Q represents every such final. That is an existing theorem,
not a new consequence of collecting more openings, and its condition is far
stronger than a roughly four-percent matching fraction.

The new bounded F19 control is more specific than this set-size observation:
eight predeclared reduced-game prefixes have 10–13 useful alpha values, but
the maximum common-two-fibre group among all optimum response/final ties has
only 4–5 alpha values, never seven. The source and scope are in
[`fork_collector_control.rs`](experiments/fork_collector_control.rs) and its
[`recorded run`](experiments/fork-collector-control-v1.log). This refutes the
naive useful-alpha-count-to-seven-common-support inference in that reduced
game. It does not establish a QM31 attack probability, impossibility of other
extractors, or absence of a valid payment witness.

## A stronger actual collector state, without assuming the missing success

Keep one root-bound raw-record cache shared across all forks whose C1/C2
roots, gamma, OOD answers and chord/interpolant inputs are identical. Each
record exposes all four slots, so it can be tested offline against every
already disclosed final in that group, not merely the final of the proof that
first opened it. Keep an individual matching-support set for each final and
the exact response0/prior/alpha parent identifiers. A change of any determining
input creates a different group; labels alone do not prove identical words.

Four distinct disclosed alpha/final pairs determine a coefficient vector Q
by four-by-four interpolation. Check every later identity
`F_j = coefficientFoldLayer 256 alpha_j Q` directly on disclosed coefficients.
Those checks need no new query openings. However, four arbitrary pairs may
produce a Q that predicts no useful later finals; the reduced control retains
this failure rather than presuming coherence. Enumerating candidate quadruples
costs up to `choose(n,4)` candidates and must be included in extractor resources.

More flexible support certificates are mathematically possible:

- Four selected branches recover Q's full four-slot agreement on their actual
  common matching support. A subsequent final with more than 255 overlaps
  with that recovered support is identified by the existing
  `SevenAlphaRecovery.common_support_identifies` theorem.
- Once branches are identified with this Q, any fibre matched at four distinct
  identified alpha values is a full-slot agreement fibre: the actual normalized
  fold residual is a degree-at-most-three polynomial and has four roots. Such
  points can enlarge the recovered support even if there was no single
  common support shared by every collected branch.

The second item is a proposed small deterministic closure lemma, not a new
retained Lean result. If all seven final identities are checked coefficientwise,
the existing `seven_represented_priors` can already prove the mixed relation
without requiring a common S. Common/overlap support is still needed to connect
that Q to the received word for recovery. Image/ordinary validity of Q alone
does not recover its original components or a payment witness.

Thus the decisive missing claim is not that successful schedules eventually
cover many points. It is that a bounded causal search obtains a useful
**coherent** quotient cluster tied to enough of the same received oracle, or
returns another valid witness, except with a quantitatively bounded failure
mass. The F19 control supplies a concrete falsifier for replacing this claim
by “seven useful scalar-compatible alphas.”

## Source and resource boundaries

The current parser model `PackedQueryRecord` derives the 621-byte record's
403-byte C1, 186-byte C2 and shared 32-byte salt projections and canonical
limbs. It does not prove root authentication or global fixed-word identity.
The pinned V7 `V7MerkleQueryExtractor` provides the matching typed hash grammar,
shared raw-query log and explicit missing-query/collision/salt failures, but
its disclosed-opening endpoint is q16, not V8 q22. Reuse the exact grammar and
proof components; do not rename the old experiment a q22 extractor.

Likewise V7's `V7Tag73RestoredQueryBatchForkController` and atomic fork scheduler
give concrete patterns for freezing the output/advance pair, discovering later
fresh slots causally, and retaining early-halt/fuel outcomes. Their q16/work
routers and old transcript bindings are not the new conditional sampling law.
These files were inspected at immutable source
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; no borrowed replay was run.

For N actual query draws, count up to 22N record incidences plus authentication
and transcript evidence, not 22 times the number of successes alone. A naive
retained-record representation uses at most `621*22*N` bytes before paths,
metadata and deduplication; this is a storage model, not measured peak RAM.
Repeated records do not add indices. One needs at least 12 q22 schedules even
to expose 256 points; 235 is a sufficient-success diversity threshold, not a
necessary number of schedules or an expected runtime. Shared cache reuse may
reduce per-branch reads, but not the obligation to elicit coherent finals.

All of this is private extractor work. The proof body remains
`697*16 + 52 + 24 + 22*621 + 2*296*26 = 40,282` bytes, with no changed verifier
operation or protocol message. No complete-transaction CU, full-view ZK,
bounded Fiat–Shamir extraction or global 100-bit claim follows from this
collector analysis. See the parent
[`fork-collector-continuation.md`](fork-collector-continuation.md) for the
combined continuation status and current evidence inventory.
