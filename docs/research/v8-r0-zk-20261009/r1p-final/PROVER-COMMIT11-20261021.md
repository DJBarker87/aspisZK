# Prover commitment continuation 11 — 2026-10-21

Branch `codex/cx-prover-commit11-20261021`, base `8e4931b1f`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit11-20261021/`.

Work in progress. No CallerLaw deletion or shipped execution certificate is claimed.

## Stage 1: byte loads and global cache

`ProverCommitOwnedBytes.readBlock_byteWord` identifies the exact extracted
four-byte load. `ProverCommitOwnedByteValue.fromLEBytes_value` proves the
little-endian numeric identity by induction on the byte list; `blockW_value`
and `byteWord_answer` identify it with the existing finite word equivalence.
No allocated stream or large numeral is evaluated.

`ProverCommitOwnedCache.next_cache` proves that each successful next-word call
preserves the identity of the cached block with the preceding answer from
the same finite oracle, and returns precisely the `wordsE` word at the current
position. Initial cache validity is unconditional. This proof includes the
refill and cached cases and retains the existing counter-capacity bound.

Accepted focused targets: J8329 (byte loads), J8332 (byte values), J8335
(cache and stream correspondence). Each exits 0, zero swaps, with only the
standard three axioms. Exact targets, source hashes, dependency fingerprints,
source revision, walls, peak RSS and all axioms/errors are in `lean/` receipts.
Drafts J8327–8328, J8330–8331, J8333–8334 are excluded elaboration failures,
not memory failures. No resource cap or recursion/heartbeat option is raised.
Only new worker-owned module/objects are installed in Env J; overwritten
versions of those modules/objects are snapshotted under this branch's host
workspace. No peer-owned source is changed.
