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

The proof stages and premise audit below are complete. Focused attempts,
including failures, are retained in
`../evidence/start-charge-20261021/manifest.json`. Deployed source and runtime
correspondence remain separate obligations.

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

### Stage 3: endpoint, zero-query corollary and premise audit

The new root is
[`OraclePortHeadlineFrozenPerAttempt.final_soundness`](../lean/OraclePortHeadlineFrozenPerAttempt.lean).
It preserves the original extractor-cost, returned-relation and abort-allowance
claims and proves

```
F ≤ (Q+34) · B + κ(Q+1161) + 2^-126 + 2^-454
B = 15 / 2^109
```

`failure_bound` states this expression explicitly for **every natural Q**,
so in particular every Q ≤ the adopted Qmax. `per_query` proves the familiar
(Q+1)·2^-100 corollary throughout that upper range, with the old 32 ≤ Q
premise deleted. `zero_queries` explicitly proves **F ≤ 2^-100 at Q=0**.
Here 34B = (255/256)·2^-100; the remaining collision and additive terms fit
inside the spare margin. The scalar inequalities are exact rational proofs;
the Q-dependent quadratic is bounded symbolically by its endpoint lemmas,
not by enumerating Q. The existing named `power454` identity is used for
the zero-query arithmetic. The initial numeric attempt's unevaluated power
is retained as a failed elaboration, not treated as a mathematical failure.

The new `final_soundness` arguments are byte-identical to the adopted
`OraclePortHeadlineFrozen.final_soundness` arguments. Evidence retains
`premises-before.lean.txt`, `premises-after.lean.txt`, and the **empty**
`premises.diff`. This comparison extracts the argument block and normalises
only the theorem name; it does not pretend the deliberately improved
conclusions are identical. `per-query-premises.diff` records precisely the
removal of `hlo : 32 ≤ Q`. Public/proof/runtime carriers, quantifiers and
failure observable are unchanged; the new Claims definition adds no
hypotheses. No source premise has been discharged, added or hidden inside
a new contract.

The bound on the restricted event follows from an actual prefix experiment
and observational equality under the memoized oracle law, not from dividing
failure probability by work or conditioning on a favourable prefix. The
adaptive prover still runs once in the full experiment, and its stored input
is never fixed under a probability measure. The prefix's arbitrary-run
fallback oracle is proved unused on every actual full run by
`recovered_eval`.

## Final verification and retained obligations

The final dependency-order pass uses exactly the accepted integrated port's
Lean environment with this packet's private object directory prepended.
`audit.json` verifies all **119** reused integrated port source/object pins,
every direct import hash, current source/receipt agreement, the final
environment, all new theorem axiom reports, the premise comparison and the
absence of existing Lean or shipped source changes. The earlier historical
cache mismatch is resolved by selecting and checking the integrated cache;
no shared object or source was rewritten.

Seven new modules pass, with **32** axiom reports, all subsets of
`{propext, Classical.choice, Quot.sound}`. All attempts, including failures
and superseded successful checks in the historical environment, are retained.
Every attempt has zero swaps, no cap or heartbeat limit was raised, and no
large recurrence, padded universe or finite-field computation was evaluated.
The full section-6 receipt fields are in `manifest.json` and each attempt:
exact command/target, exit, wall time, peak RSS, swaps, source revision/hash,
dependency fingerprint and complete `#print axioms` output.


| Final target | Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps |
|---|---:|---:|---:|---:|---:|
| `StartChargePrefix` | 7 | 0 | 8.602 | 3,644,637,184 | 0 |
| `StartChargeHit` | 3 | 0 | 8.450 | 1,534,640,128 | 0 |
| `StartChargeCompletion` | 6 | 0 | 24.729 | 3,578,626,048 | 0 |
| `StartChargeClean` | 3 | 0 | 13.162 | 3,626,336,256 | 0 |
| `StartChargeProbability` | 2 | 0 | 18.060 | 3,610,476,544 | 0 |
| `StartChargeNumeric` | 2 | 0 | 12.699 | 3,594,420,224 | 0 |
| `OraclePortHeadlineFrozenPerAttempt` | 1 | 0 | 12.048 | 3,604,594,688 | 0 |

The manifest retains 24 attempts (12 failed); the final pass totals 97.750 compile seconds and peaks at 3,644,637,184 bytes RSS.

The adopted port integration evidence is reused; no unchanged frozen
regression, Rust/SBF rebuild, Aeneas replay or runtime suite was rerun. This
packet is additive focused proof evidence, not a new coherent release rebuild.
No shipped source changed, so the conditional frozen-ELF identity rebuild
gate was not triggered. No other cone, lean-candidate, wallet or key changed.

The probability-level counting obligation is closed. **The deployed target
is not yet established**: the unchanged `AcceptedRunJoin D rust` and
`StoredCarrierBinding D rust P runtime` still need concrete deployed-source
and runtime proofs. The per-cone work and frozen source/artifact obligations
in the existing cone audit remain with their assigned owners. The next
integration deliverable is adoption of this endpoint with those same joins,
followed by the release dependency-closure replay when the source joins are
ready. Nothing is pushed or merged by this worker.
