# Finish candidate: complete dot-product call trace

PROVED for the unchanged generated dot helper in the separate, unadopted finish source candidate:

- A continuing loop step reads the current message coefficient and selected weight, successfully pushes that pair into the dot accumulator, and advances the index by one.
- A successful loop either returns a source error or reaches the end through that sequential chain. A pending successful early return is impossible.
- Successful `finish_query_dot` starts with `newDot`, processes the whole slice from index zero, and calls `finishDot` on the accumulator returned by that chain. Per-index decoder/push successes are derived from this success, rather than assumed.
- A mathematical prefix invariant can be transported along the chain once the concrete successful-push law is proved.

The proof uses symbolic induction on remaining length. It preserves source error behavior and does not unroll the array. Concrete dot arithmetic, decoder semantics and source/effect equivalence of the candidate with the frozen verifier remain OPEN. This packet does not adopt the source candidate or close R14.

Three focused NUC targets passed with -M4400, 1 GiB high / 2 GiB max / swap-zero scopes and standard printed axioms. Exact source/import/compiler/object hashes, commands, timing, RSS and swap are in the manifest and receipts. No binary, resource-option override or new axiom is included. The generated candidate owner is reused by exact source/object hash from the preceding candidate packet; it was not recompiled unchanged.
