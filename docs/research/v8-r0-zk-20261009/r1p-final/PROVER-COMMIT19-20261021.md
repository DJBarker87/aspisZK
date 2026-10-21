# Prover commitment part 19 — seed event and shipped experiment

Base `28776b162`; branch `codex/cx-prover-commit19-20261021`.

Work in progress. Target not yet established. This report is updated at each
committed stage. Concurrent-worker modules SourceIdentification,
RustRuntimeJoin and PrivacyR1FinalRelease are untouched.

## Scope and mathematical accounting

D127 authorizes a seed-guess exception and its explicit privacy loss. The
constructed model has no simulator-seed coordinate; the new event must use
an independent retained seed, rather than assuming that an existing model
coordinate is independent of its own observable history. The global event
must be counted once, outside the eight-attempt union.

## Evidence

Focused Lean checks run on the NUC, one at a time, in env J using unused
attempts 8675–8799. Each scope has MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0 and TasksMax=64. Exact snapshots and JSONL receipts are stored
in `docs/research/100bit-spend-path-20261013/evidence/prover-commit19-20261021/`.
No full frozen-manifest replay is claimed until the focused dependency cone
is green. Source revision, exit, wall time, peak RSS, swaps, dependency hashes
and full axioms lines are retained in the per-attempt receipts.

## Stage 1 — seed accounting and premise transport

`ProverCommitSeedEvent19.seedPoint` tests the exact source domain and 32-byte
seed prefix. It deliberately also charges malformed suffixes in that namespace.
`source_point` proves containment of every source coin address, for every
attempt, stream and counter. `seedPoint_unique` proves that any query names
at most one seed. `seed_mass` proves the resulting q/2^256 upper bound for a
list depending arbitrarily on all model coins and adaptive answers, independent
of the separately retained seed. No seed carrier is enumerated.

`augmented old queries i (m,seed)` is
`old i m ∨ (i = 0 ∧ seedGuess (queries m) seed)`.
`old_contained` and `union_mass` prove containment and a single global charge,
not eight charges. `ProverCommitSeedJoin19.of_old` constructs an actual product
extension of the old coupling; the runtime/model observations do not change.
This proves implication of old certificates to augmented certificates. Proper
inclusion for each adversary is not asserted (an observer making no queries
has no seed-guess event).

`ProverCommitObserverQueries19` exposes the exact adversary-only `runLog`
suffixes in real and ideal games, including failure exits; both lengths are
at most W.qmax. The query functions retain the original shared table and
programmed fallback. They do not replace adaptive queries by fixed addresses.

Accepted focused checks: J8681 seed events (exit 0, 2.12 s, 4,042,740 KiB),
J8683 generic join/numerics (exit 0, 2.45 s, 4,060,364 KiB), J8685 query caps
(exit 0, 2.05 s, 4,037,844 KiB). All swaps 0; all printed axioms are subsets
of `[propext, Classical.choice, Quot.sound]`. Revisions are `28776b162` plus
exact snapshot hashes. Earlier attempts are retained and excluded: the errors
were local rewrite/decider/instance normalization, repaired without changing
resource limits. Existing shared objects were not overwritten in this stage.

The numerical proof is symbolic: at q ≤ 2^64, one seed charge is at most
2^-192; two coupling sides add at most 2^-191. The old conservative upper
bound plus these terms is at most 8·2^-109 = 2^-106 < 2^-100. No old loss is
removed or hidden. Connecting this result to the deployed signature is the
next stage; concrete shipped execution and full simulator history remain open.
