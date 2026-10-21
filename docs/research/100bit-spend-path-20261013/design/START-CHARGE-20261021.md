# Accepted transcript start charging, 21 October 2026

Branch `codex/cx-start-charge-20261021`; binding target:
[SECURITY-CONTRACT-20261021.md](SECURITY-CONTRACT-20261021.md).
This packet changes only new Lean modules, its focused tooling/evidence,
and these design notes. Shipped crates and other workers' cones are read-only.

## Mathematical boundary

The adopted full-log event includes any decoded classifier chain, including
chains first-read by terminal Merkle authentication. That event really can
have more than Q+34 starts. It is not the event needed by the extractor:
a classifier hit in the submitted transcript has its sampler chain read
before the terminal authentication begins.

The charged experiment executes the adaptive prover, canonicalises its
proof, runs the 33 sampler rows, and constructs metadata from their causal
cuts. It stops before terminal authentication. This is a new observable
experiment, not a replacement verifier and not a restriction on adversaries.
The full experiment remains the target for collisions, acceptance,
extraction cost and runtime transport.

## Proof stages and evidence

Work in progress. Focused attempts, including failures, are retained in
`../evidence/start-charge-20261021/manifest.json`. No release-complete claim
is made until the new endpoint and its complete premise audit compile.

### Stage 1: chronological prefix

`StartChargePrefix` constructs `charged D P`. `same_transcript` proves exact
public/proof equality with the adopted full experiment; `chronological_prefix`
proves its whole oracle log precedes the terminal suffix. For every sampler
row (not merely accepted runs), `transcript_start_read` and
`transcript_start_prover_or_followed` place its start in the prover/followed
sampler log. `first_start_before_terminal` preserves that address's actual
first-read index in the full log. Thus a terminal-only first read cannot be
the start of a submitted transcript chain. `starts` proves Q+34 directly,
including the row-26 reseed, for every Q. `recovered_eval` reconstructs this
prefix from the full record without querying a fallback oracle.

Focused stage-1 compile: attempt 6, exit 0, 19.099 seconds,
3,580,035,072-byte peak RSS, zero swaps; ten axiom reports, each a subset of
`[propext, Classical.choice, Quot.sound]`. Exact target, source hash/revision,
import fingerprint, command, logs and timing are in the manifest and attempt
directory. Attempts 1–5 retain ordinary syntax/elaboration errors. This is
focused cached-object validation, not a frozen release replay.

### Stage 2: completion, clean event and restricted mass

`StartChargeHit.hit_implies_chain` localises the existing indexed-round
argument to an arbitrary specified log with pointwise completion. It has no
probability or acceptance hypothesis. `StartChargeCompletion.decodes`
instantiates the existing binary RWire completion on the charged prefix;
`hit_in_prefix` sends a literal bad submitted round into that prefix's
classifier event.

`StartChargeClean.accepted_facts` obtains the existing full-run Checks,
extractor word alignment and admitted tag from frozen acceptance.
`clean` proves the original full experiment's `CleanAcceptedModel` with
bad event = full-log collision OR prefix-only hit. Prefix collision freedom
is inherited from full collision freedom; no extra collision event is added.

`StartChargeProbability.hit_mass` uses the finite-support oracle law to
identify the prefix observable's mass under the full adaptive experiment
with its mass under `charged D P`. `restricted_union_bound` then applies
the existing per-start density B and Q+34 start count. `failure_bound` gives
exactly κ(Q+1161) + (Q+34)B + 2^-126 on the **unchanged full-run**
accepted-extractor failure event, for every Q. There are no additional
source, probability, transcript-format or lower-query hypotheses.

All five modules through the probability bridge have successful focused
checks with standard axioms and zero swaps. Completion attempts 1–4 retain
elaboration timeouts (and one invalid reducibility annotation); making
protocol projections and hit predicates opaque, and applying completion
pointwise, replaces the accidental unfolding. No resource/heartbeat cap
was raised. The symbolic decoder completion itself already passed in those
attempts; failed recovery terms are never accepted.

Before the final endpoint check, cache comparison found 14 differing
historical objects among the integrated port objects available through the
copied historical launcher. `cache-equivalence.json` retains the comparison.
The final pass will use the latest `port-integrate-20261021` environment and
recheck the new modules in dependency order. This is a specifically
identified dependency-environment change, not an unchanged regression.
