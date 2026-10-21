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
