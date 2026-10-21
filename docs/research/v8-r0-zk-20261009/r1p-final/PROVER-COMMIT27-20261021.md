# Prover commitment part 27

Base `26b922be6`; branch `codex/cx-prover-commit27-20261021`.
Target not yet established. This report is updated at each verified stage.
The final job-specific Env J range 7636–7699, then 7700–7799, is used after
checking the shared receipts. No shipped or concurrent-owned file changes.

## Stage 1 — explicit CoinOracle state and product marginals

`ProverCommitCoinTape27` introduces a state-passing Digest32 interface returning
both digest and full updated state: cursor, optional recorded table and sticky
collision flag. `call_preserves` identifies source-order control with the
explicit-state reference under the D133 named ordered-map contract.
`sequence_preserves` lifts this equality to arbitrary finite adaptive call
trees, retaining the complete final state and ordered query/answer history.
`cursor_history` counts every call, including duplicate and exhausted reads.
The old pure generated dictionaries are not overwritten or silently given a
stateful meaning. This new interface is an owned formal reference, not yet an
Aeneas extraction of the complete caller cone.

`ProverCommitCursorMarginal27` transports both D134/D135 product marginals
through deterministic initialization and effectful adaptive evaluation.
`ProverCommitTranscriptTape27` binds the tape to the actual 115 stream-0
addresses of the existing product oracle. `stream_disjoint` and
`transcript_unchanged` prove stream-3 rejection packing leaves every transcript
coin unchanged. `product_coins` identifies the whole cursor-indexed tape,
including its zero fallback. `execution_law` retains final state and complete
history in the tested observation; it does not post-select on a final cursor.
No new randomness, freshness premise, or source-join trust item is introduced.

J7638 passes the three state/sequence audits (2.07 s, 4091608 KiB RSS);
J7640 passes three marginal audits (1.85 s, 4087260 KiB);
J7641 passes four concrete-tape audits (1.89 s, 4164988 KiB).
All exit 0, zero swap, standard axioms only. Receipts record exact modules,
source revisions/snapshots, dependency hashes and full axiom lines. J7636 and
J7637 are retained parse/instance failures; J7639 is a passing predecessor
whose unused rejection-coin accessor was removed before J7640.

The first combined Kani RefCell/reference gate timed out at 120 s. It is not
verification; a smaller fixed-input-length gate is in progress. Table operations
use the D133 approved contract projected to the current query key, rather
than another attempt to verify B-tree internals. Native cursor arithmetic is
checked only below usize::MAX; the Nat model still needs its bounded-caller
connection at the actual execution boundary.

## Still open

Re-extraction and source binding of the extended effectful caller interfaces;
concrete builder/checker/retry, commitment programming and serialization joins;
`shippedProverExperiment`, both complete WholeRunJoins and endpoint deletion.
The generic call-tree theorem does not assert that the unchanged generated
semantic/circle/control callers already implement this call tree.

## Stage 2 — actual extracted state-passing oracle

`harness/effect27.rs` is an owned state-passing CoinOracle reference with the
D133 recording callback. Charon and Aeneas extract its complete operation,
including returned state; no external extraction templates are used.
The first byte-comparison loop hit Aeneas `InterpBorrows.ml:2731`; an explicit
comparison replaced it. The monolithic 32-comparison proof hit Lean's default
heartbeat budget, so four eight-byte source helpers and named symbolic lemmas
replace it. No heartbeat, recursion or memory limit was increased.

`AspisR1CoinEffect27` contains the resulting actual generated API.
`ProverCommitExtractedCoin27` proves every byte-comparison helper and their
composition against complete array equality. J7652: exit 0, 15.35 s,
4247436 KiB RSS, swap 0, nine standard-only axioms audits.
`ProverCommitCoinCall27.call_exact` proves the complete generated call against
the reference effects, universally over finite vector length, cursor, table,
query and initial collision flag. It includes the actual wrapping machine
increment. `read_total` proves every read, including exhausted-tape zero fallback,
is defined. J7656: exit 0, 2.04 s, 4164120 KiB RSS, zero swap; both audits standard.

`extracted-call-v5` checks the literal shipped RefCell body against the exact
Rust reference used in the successful extraction: all three tape-length gates
(0/1/2) pass, arbitrary pre-overflow cursor, arbitrary full digest bytes,
recording on/off, prior answer and collision flag. Exit 0, 20.571 s,
1586016 KiB RSS, zero swap. It uses the separately verified universal full-byte
comparison contract (`different-v1`: exit 0, 1.988 s, 210496 KiB, zero swap).
The map implementation is a projection of the D133 trusted map contract to the
current key; these are bounded library/control gates, not verification of all
native vector lengths or B-tree internals. The universal extracted equation
is a separate Lean theorem. Earlier timeouts/unwind/compile diagnostics are
retained and excluded. The accepted gate records prelaunch reservations.

Actual owned effectful caller extraction has also succeeded for the literal
semantic/circle three-read helper and suffix block/query-materialization
skeletons (`callers27.rs`); their source equations and whole-source composition
are the next stage. The policy, retry, native trace and serialization boundaries
are not discharged by this interface extraction.
