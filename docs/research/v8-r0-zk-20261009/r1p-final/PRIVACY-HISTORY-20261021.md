# Privacy history split — 2026-10-21

Branch `codex/cx-priv-history-20261021`, base `d93756b49`.

## Stage 1: exact interface split

`QueryScanHistorySplit` separates the **actual** fields of `ScanCoupling`.
`ScanExecution` retains cp, eight coupling-space events and whole-observation
agreement off their union. `ProbabilityContent` is exactly the deleted mass
field. `exact_split` proves equivalence with their conjunction.

There is an obstruction to deleting the mass field with unconstrained events:
`vacuousExecution` supplies an execution join between any two observations
with coupled randomness by choosing all events True. `zero_one_no_scanCoupling`
proves that the constant Boolean observations 0 and 1 have no ScanCoupling.
Thus `probability_not_execution_content` is a compiled counterexample to
recovering that field from the literal execution-only remainder.

A sound interface must fix the events independently of the source join.
`ModelExecutionJoin source model bad` does so, with no probability fields.
Its `toScanCoupling` transports a separately proved model law via cp.meanM;
it does not assume independence between attempts or enumerate any carrier.
This is a usable separation, but it does not assert that the law has been
proved for actual ROM query failures.

Focused env J attempt 9801: exit 0, wall 2.14 s, peak RSS 3,517,108 KiB,
swaps 0; all five theorem audits use only propext, Classical.choice, Quot.sound.
Attempt 9800 retained a local rewrite elaboration failure, fixed by explicitly
instantiating cp.meanM at the event indicator. Complete source revisions,
SHA256, dependency fingerprints, launcher output and timing are in
`history-attempts-9800-9999.jsonl`. New sources/objects only; own drafts are
snapshotted under `snapshots/codex-cx-priv-history-20261021/<attempt>`.

## Stage 2: adaptive shared-oracle histories

`QueryScanIndependentHistory` proves the model-level law that is actually
available on independent coins: the retained LE eight-word, low-18-bit parser
is a measure-preserving projection, eight blocks flatten to 64 independent
words, and reached failure is bounded by `scanProbability`. The reachability
predicate is arbitrary and may depend on every coin. The eight-attempt result
marginalizes the selected attempt by `mean_eval`; it assumes no independence
between the eight failure events. This reuses the existing byte/word bijection
and symbolic first-22 failure-small-range theorem.

These are **unconditional masses of reached-failure subevents**, not masses
conditional on an arbitrary already-revealed shared-oracle history. The latter
is a different statement. Shared-ROM addresses may repeat.

Env J attempt 9805: exit 0, wall 2.24 s, peak RSS 4,028,516 KiB, swaps 0;
six standard-axiom audits. Earlier 9802/9803 were elaboration failures resolved
by explicit equivalence/coordinate arguments and symbolic cardinality
transport; no limits were raised or concrete finite universes reduced.

## Endpoint signature and before/after

Pending final statement audit. No unconditional replacement endpoint is claimed.

## Stage 3: compiled shared-ROM obstruction

`QueryScanSharedHistoryObstruction` uses the exact retained transcript grammar:
`squeezeAddress s = ans s ++ [1]`, `advanceAddress s = ans s ++ [2]`.
An advance self-loop `H (advanceAddress s) = s` forces every query state to s
and every query block to the same answer. A symbolic scan induction proves
that scanning repeated copies of one block can accept at most eight distinct
words. Consequently `finish` fails even at the constructed parser's own
`stop done` endpoint. There is no 64-word recurrence evaluation.

`LoopHistory bound` is the existing finite ROM table conditioned on the
advance answer at zero being zero. It is inhabited by the zero table.
`reached_shared_history_failure_mass` proves failure mass **one** on this
history; `reached_shared_history_not_bounded` contradicts the proposed
`scanProbability` bound on every history. For bounds at least 33 this is an
in-domain read, so the phenomenon does not depend on out-of-domain fallback.
The generic `finite_rom_zero_history` induction proves the all-zero history
is reachable in `LazyFrozen.runC` for *every* address program and every ROM
bound, hence also the constructed protocol's full scheduled read program.

This disproves the **conditional-on-every-history** demand, not the existing
unconditional `ScanCoupling.R_rom_query_word_history` field. That field is
only a bound on the mass of each chosen coupling-space event; it does not
quantify conditional probabilities over histories. No claim is made here
that every possible choice of endpoint ScanCoupling is impossible.

The exact missing fact is a source/model join preserving first-read addresses
and answers and identifying a **fresh** 64-word stream outside already charged
collision/prior-read events, together with whole-observation agreement on
those excluded histories or a reduction that pays for them. No Rust fact can
make a retained shared-oracle repeated read fresh. A correct repair must
separate the independent scan failure from collision/prior-read events and
prove where their mass is charged; it cannot assign the entire conditional
self-loop failure the independent-word bound. The existing collision budget
in modelError may support a redesigned combined reduction; this packet does
not silently charge it twice or change the endpoint's error.

Env J attempt 9808: exit 0, wall 2.66 s, peak RSS 4,038,828 KiB, swaps 0;
13 theorem audits, all standard or subsets. 9806 is a green predecessor;
9804 was a variable-substitution elaboration failure. Only this branch's
new module was replaced on the host, with its source/object snapshotted.
