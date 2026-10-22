# S4 selected packed return for tx1 and tx2 (source-only)

This focused Lean module derives the selected packed-word result for each of the ten tx1 calls and twelve tx2 calls from the same caller-success execution and callback output already retained by the green local-batch proofs. It adds only the parsed wire and exact proof length, the model query vector, and the existing kind-0/kind-1 authenticated recovered-map predicates. The returned evidence preserves the exact callback `.ok values`; it does not assume a guessed output or uniqueness of queried indices. Gamma/query-transcript identification remains an upstream boundary.

The per-call transport uses the selected packed-return theorem and the byte-framing lemma: kind 0 payload is the first 480 opening bytes, kind 1 payload is the following 128. This proves framing and same-output interpretation; it does not claim Merkle authentication beyond the supplied existing authenticated-map predicates.

Both exported theorems are named in `receipt/lean.log` and have standard axioms `[propext, Classical.choice, Quot.sound]`. The focused run was Lean 4.32, `-j1 -M4400`, with no dependency builds. Exact launch revision, argv, profile, import/object pins, RSS, swap, and wall time are recorded under `receipt/`. The recursively checked OLean import closure contains 7,531 modules with no missing imports. No compiled objects are included.

Attempts v1-v4 were nonaccepted setup/elaboration diagnostics and remain under `/tmp/s4-selected-packed-tx-consumers-v1` through `v4`; v5 is the accepted source snapshot.
