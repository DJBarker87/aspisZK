# Causal table/log focused Lean evidence

This bundle records focused NUC compilations for a deterministic bridge between finite trace logs and the Merkle recovery lists. It includes the concrete C1 finite candidate-cardinality cap, lookup extensionality for logged records, trace replay and membership facts, the first-read cut representation, and the recovery/stability theorems for C1, C2, and the folded commitment. The checkpoint reaches these 14 component modules through three direct imports and audits 30 imported declarations.

The proved scope concerns a consistent logged-table representation and the full-trace collision exclusion used by the recovery arguments. It does not provide an efficient list-decoder implementation, a numerical protocol-security estimate, or a Rust/source-refinement theorem. The C1 result bounds the specified mathematical candidate list for selected words; it does not parse committed bytes or implement efficient list decoding. The functional-table connection retains explicit consistency, replay identity, read-budget, and event premises. Its hash-separation fact is derived from the existing full-trace collision exclusion.

## Provenance and audit

- Source base: `e21211727fc6ad53a2ef014d3fa3dda72037cef0`.
- Fifteen final modules have successful focused receipts. The attempt archive preserves 39 receipt-backed attempts: 21 failed, 3 superseded green, and 15 final. The empty `R1C1PartialCandidates-c1partial-a.source.lean` is preserved separately as pre-snapshot staging; it has no receipt and is not counted as a compile attempt.
- `source-manifest.json` records the local source stem, remote module identity, final suffix, exact source and object hashes, per-attempt receipts, cgroup/resource results, runner hashes, and allowed axiom audit.
- The final `R1CausalTableCheckpoint-causal-table-checkpoint-a` receipt is exit 0, 1.29 s, peak RSS 3,134,416 KiB, swap 0, under `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`. Its 30 printed declaration audits use only `propext`, `Quot.sound`, and `Classical.choice`.
- All exact attempt snapshots match their receipt and SHA sidecars. Superseded green versions of `R1MerkleLeafLookupExt` and `R1MerkleLogExt` are retained; `R1LaterTableStability-later-table-stability-c` is also retained as a superseded green source preceding the final no-unused-arguments version.
- Final objects are stored in `objects/causal-table-objects.tar.gz`; its member-level hashes and sizes are in the manifest. Runner/environment snapshots are preserved under `runner/`.

The evidence is limited to these Lean module statements and focused compilation receipts. It does not establish end-to-end protocol security or extraction closure.
