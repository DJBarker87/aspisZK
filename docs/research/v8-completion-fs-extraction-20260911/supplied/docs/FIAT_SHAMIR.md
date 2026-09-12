# Full Fiat–Shamir work plan and first attempts

## 1. State the security experiment before proving a bound

Fix the exact profile, verifier byte grammar, public statement and runtime
context. Define the class of adversaries and the resource budget: total fresh
SHA queries, total calls including cache hits, time, memory, extraction/replay
work, and the number of adaptive statements/proofs. State whether the intended
result is single-theorem knowledge soundness, adaptive multi-theorem knowledge
soundness, simulation soundness or another notion. These are not interchangeable.

The end goal must have the form:

    for every permitted adversary A,
    Pr[real verifier accepts A's output and the specified extractor fails
       to return a witness satisfying the independent payment relation]
       ≤ ε(profile, Q, time, extraction budget, instance count).

A target such as ε≤2^-100 is evaluated at explicitly declared budgets. Do not
say that a success probability bound is independent of arbitrary unbounded
oracle search. Conversely, do not mechanically multiply every existing term by
Q if a sharper source-aware argument can legitimately avoid that loss. Prove
which opportunities the actual adversary has and charge precisely those.

An interactive conditional residual of about 104 bits is not by itself a
resource-bounded FS theorem. `security.py` contains deliberately labelled
restart diagnostics: sixteen independent opportunities already use essentially
all four bits of this particular residual ceiling. This is **not an attack on
Aspis or a proof of a necessary loss**; it is a guard against inventing a free
reduction from one prefix to every adversarial attempt.

Primary background: Bernhard–Fischlin–Warinschi, Adaptive Proofs of Knowledge in
the Random Oracle Model, ePrint 2015/648, explicitly distinguishes adaptive
knowledge from weaker notions. Do not apply its protocol-specific results to
Aspis without checking assumptions. https://eprint.iacr.org/2015/648

## 2. Bind the literal transcript, not a invented replacement

Fill config/TRANSCRIPT_BINDINGS.json from the repaired source. For every SHA
call record exact byte parts, widths, endian conventions, counters, prior state,
role and first-consumption boundary. Include version/profile/release framing,
public statement, program/pool/asset/registry context, and earlier commitments
where the actual source uses them. Check missing bindings rather than assuming
that names such as `contextDigest` contain everything intended.

Do not change protocol bytes for convenience. The Python Receipt/Recorder
metadata deliberately does not prepend role labels. Two roles using identical
literal input bytes get the same hash answer: a proof must classify such aliases
rather than pretending that roles create independent oracles.

Prove the serialiser's intended injectivity or bounded ambiguity under its
actual fixed/length-delimited grammar. Reject malformed lengths and noncanonical
fields exactly as the parser does. Hash-input collisions from ambiguous
serialisation are deterministic defects, not 2^-208 random hash collisions.

Use synthetic fixtures for trace publication. A full oracle log can contain
private material. Keep private witness-bearing logs local; a redacted public
log is not a substitute for a privately replayable exact trace.

## 3. Full-width lazy oracle and first exposure

OracleCache.lean provides deterministic cache transitions. UniformStep and
LazyROHazard give a finite reference-machine fresh-hazard argument. The state
can contain the full prior adversarial history; requests precede fresh coins.
Cached requests reuse their answer and do not acquire fresh independent entropy.

Connect that machine to actual SHA query events, including the adversary's own
queries, adversary-first/cache-hit cases, verifier queries and permitted replay.
The algorithmically chosen message may depend on all earlier answers. Every
local target set must nevertheless be fixed before its charged fresh answer.

`FirstExposure.FirstAt` makes the selected occurrence unique. Its production
instance must be the actual accepted proof's occurrence, not merely another
coordinate satisfying a work predicate. `UnresolvedTargets` supplies the useful
whole-domain cardinality bound for C1/C2 resolver images; adaptive choice of
opening position does not multiply that fixed target cardinality.

Do not use the fresh-hazard theorem to discard cached bad events whose target
was chosen only after the cached answer. Show such events map to an earlier
legitimate exposure, are covered by another named event, or remain unbounded.
The tests include a counterexample: selecting the singleton target {answer}
after sampling yields probability one even though its cardinality is one.

Full 256-bit SHA answers stay visible to the adversary. DigestProjection models
prefix×tail counting for 208-bit targets; derive the actual byte/bit bijection
rather than limiting the adversary's view to 208 bits.

## 4. Chronological source prefixes and stopping times

Build the C1 prefix from the actual execution before lambda/chi. Build C2 from
its actual later commitment phase before OOD/gamma. Record exact cut indices,
prefix nesting, response consistency and the unread suffix.

The repository's TraceIncludedInLog membership hypothesis is not a stopping-time
or chronological-prefix theorem. ChronologicalPrefixes supplies actual list
prefixes and cut noninterference, but identifying source cut locations is still
the caller's proof obligation. Handle roots first queried by the adversary and
roots whose relevant paths are not fully available at the cut.

Do not choose a prefix retrospectively because it makes extraction work. Its
selection must be a source-determined stopping rule. Prove that changing later
coins cannot change already frozen words, commitments, targets or source state.
For restored/forked executions, include the precise cached state and source
cursor used to resume, not just an abstract equality of final transcripts.

## 5. Exact samplers and finite aborts

For each scalar/nonzero-QM31, circle/OOD, distinct second OOD, and q22 query
sampler, freeze:

- raw hash input and output bits consumed;
- exact field decoding and noncanonical rejection;
- counter/retry limits and fresh versus cached inputs;
- domain exclusions, equality/duplicate checks and abort branch;
- the source state returned after success or abort.

`sampling.py` computes unconditional finite-retry distributions from an explicit
raw decoder. It does not guess the selected SHA-to-QM31 decoder. Its
masked31_decoder is only a candidate diagnostic. Replace or bind it only after
reading the exact selected source.

RejectionKernel.lean proves the recurrence a+r·previous and retained abort r^n.
A one-step decoder preimage count must produce its input atom bounds. An
unconditional success atom can be bounded without conditioning away aborts.
The second OOD atom must be uniform/bounded for every reachable first-sampler
terminal history. Marginal uniformity of each draw does not imply the joint law.

DistinctPair supplies the ordered off-diagonal sum. Instantiate it with the
actual sequential sampler and its distinctness guard; obtain m(m-1)/(N(N-1))
only under those proved laws. DistinctQueries supplies the corresponding
without-replacement arithmetic and explicitly positive denominators.

For query duplicates/retries, prove distribution and original query ordinal,
not merely set uniformity. The relation uses rho^(i+1); sorting Merkle descriptors
must not reorder the semantic injection. Every rejected or exhausted sampler
must follow its actual source path, not become an uncharged success case.

## 6. One causal strategy across all continuations

The new same-body repair must not use constant callbacks capturing a completed
body. CausalPrograms has a finite interaction syntax and a prefix theorem where
the first request cannot depend on its own or future coin. The actual adversary
must be translated into one such legal program/replay object from the same
initial state and committed prefix.

Then construct the selected ideal strategy uniformly. On the realised run,
its consumed values equal the source values. Across alternate suffixes, prior
values remain fixed. Allow the actual final polynomial to depend on alpha0 and
later responses on only the challenges already revealed. Do not strengthen the
adversary away by assuming an honest strategy, a polynomial received word or a
preselected adaptive final.

A statement of the form `forall completed run, exists ideal execution` is too
weak to transport probabilities: a separate ideal strategy could be chosen for
each successful run. FiatShamirTransport exposes the missing law-preserving
mapping. It is intentionally a conditional CONSUMER, not evidence that such a
mapping has been produced for Aspis.

## 7. Authentication game hops and explicit resources

Retain the shared raw truncated-digest collision, C1 late target and C2 late
target alternatives. Their targets must come from the same actual frozen
resolvers. Let Q count the charged fresh oracle queries. Standard candidate
ceilings are Q(Q-1)/2^209 for 208-bit birthday collisions and Q·M/2^208 for a
fixed M-target hit, subject to the actual exposure/target-fixation arguments.

These are bounds, not estimates of observed attacks. They are meaningful only
at a stated Q. Do not borrow the 104-bit generic birthday work scale and call it
a Q-independent failure probability of 2^-104.

Combine C1 and C2 target images by one conservative union if needed. Preserve
one shared collision event instead of summing duplicated copies from every
layer unless the overcount is explicitly accounted for. No independence is
required for an ordinary union bound. Do not count raw query calls as fresh
ones; do count real repeated computational work in the extractor runtime.

The combined root-product degree cap 90,407,376 with
N=(2^31-1)^4-(2^31-1)^2 gives an approximately 195.14-bit ideal pair expression.
It still requires the actual sampler law. This does not establish the entire
FS authentication ledger.

## 8. Extraction/replay coupling

FrozenAccess refuses missing preimages. ForkReplay proves deterministic
prefix consistency and accounts for repeated suffix execution; it does not
prove enough useful forks exist. `forks.py` retains abort, censored and incoherent
branches and counts all work. A count of useful forks is not necessarily a
coherent interpolation group.

Produce an extractor algorithm under its explicitly permitted access. Show
where candidate/sample information originates. Formalise decoder correctness,
completion and runtime on its actual representation. The image/circle-to-GRS
transform, canonical M31/QM31 descent, field basis and 16-column common support
must be connected to the authenticated data. The prime-field Gao reference is
not that source implementation.

For a probabilistic extractor, specify its private randomness and its
independence from the committed word. Charge failure once for the common sampled
support when a joint theorem allows it; do not add or remove a factor of 16 by
intuition. Do not use the rare failure of a near-word decoder as coverage of all
accepted far/absent-anchor cases.

## 9. Compose the actual payment failure experiment

The complete source event must imply either a valid checked witness or one of
the precisely named charged events. RecoveredHigh is an algebraic predicate and
cannot simply be removed from accepted-but-unextractable mass. A producer must
show it yields the permitted algorithm's complete payment witness, or its
remaining failure is a separate term.

Use GlobalLedger only after all eight named event families are instantiated
with one consistent measure, source profile and parameter convention. The
number eight is bookkeeping, not a claim that exactly eight primitive events
suffice. Combine/refine categories explicitly and update the independent
statement. Unknown source binding, sampler law, extractor completeness or
adversarial search factor is not zero.

## 10. Full-view adaptive ZK is a separate theorem

Do not regard soundness coupling as simulation. A simulator may need oracle
programming at inputs not queried before; any guess/programming conflict needs
its own event and budget. Roots, salted leaves, openings, masks, ordinary/OOD
answers, semantic messages, nonce behaviour, aborts and all observable hash
queries belong to the same joint view.

MaskTranslation proves an additive bijection and a linear shift identity;
masking.py tests witness shifts against the mask-map column space. Those do not
handle nonlinear positivity/inverse fields or the adaptive authenticated view.
The exact repaired profile must be simulated without access to the secret
witness. State whether the claim is single or adaptive multi-theorem ZK.

## Promotion checklist

F1: actual transcript/statement binding.
F2: source chronological first exposures and full-width lazy oracle.
F3: all exact sampler laws with aborts and returned history.
F4: one uniform strategy construction and law-preserving source coupling.
F5: explicit resource-dependent authentication and repair ledger.
E1/E2: permitted extractor plus complete checked payment witness.
G1: exhaustive source failure partition plus exact rational threshold.
Z1: independent full-view adaptive simulation.

None is green merely because the corresponding generic draft in this folder
compiles. Its actual selected-source producer is the acceptance criterion.
