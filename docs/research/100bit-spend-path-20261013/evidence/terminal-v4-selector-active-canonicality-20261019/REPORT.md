# Generic selectors close the active-loop mask premise

The actual current selector loop, outer selector-mask sum and active-literal loop now preserve canonicality for arbitrary masks, given canonical input cells. The active-loop proof derives the selector call's successful result from the same successful generated execution with a generic pair-bind inversion lemma. It no longer takes `maskStepOK` or enumerates the seven nonzero masks. The wrapper specializes the actual 64-step `active_literal` call starting from ZERO.

The 64 high cells and 16 low cells remain explicit canonicality premises. This is not a theorem that the actual preparation code constructs those arrays canonically, nor a whole-terminal or whole-verifier soundness theorem. It is a stronger replacement for the conditional active-loop leaf published at `c7cf97c58`; that older immutable packet remains unchanged. The new readable source modules are isolated in `lean-candidates/current-terminal-selector-active-20261019` so the two compiled versions are not confused.

| Checked receipt | Exit | Wall seconds | Peak process RSS bytes | Process swaps |
| --- | --- | --- | --- | --- |
| active-literal-axiom-audit-receipt.json | 0 | 13.86 | 2,190,245,888 | 0 |
| active-literal-canonical-from-inputs-receipt.json | 0 | 12.11 | 2,239,774,720 | 0 |
| active-literal-loop-canonical-receipt.json | 0 | 41.26 | 1,536,901,120 | 0 |
| bind-pair-success-receipt.json | 0 | 4.93 | 2,194,554,880 | 0 |
| result-index-success-receipt.json | 0 | 16.22 | 2,183,790,592 | 0 |
| selector-loop-axiom-audit-receipt.json | 0 | 9.33 | 2,213,183,488 | 0 |
| selector-loop-canonical-receipt.json | 0 | 13.52 | 2,214,215,680 | 0 |
| selector-mask-sum-axiom-audit-receipt.json | 0 | 12.72 | 2,146,172,928 | 0 |
| selector-mask-sum-canonical-receipt.json | 0 | 14.67 | 1,916,420,096 | 0 |

Green audits contain only standard axioms `propext`, `Classical.choice`, `Quot.sound`; the generic pair-bind inverse needs only `propext`. Exact sources, objects, source revisions, compiler and direct-import hashes, ordered roots, commands, timing, aggregate Lean RSS limits and process swaps are in the immutable packet. The local machine had prior system swap usage; zero process swaps is not a machine-wide zero-swap claim. No full manifest replay was run.

Publication validated all 49 payload hashes and nine successful source/object/receipt triples. Archive SHA256: `f580dd24bd26516ce2fea6b75cb0832b12b9e7b9b679438979ff3b25e44b505d`; manifest SHA256: `68267b6772d191b5ae9d6849676909b298c71e5fc295df819f7b76724894e8d6`.

Earlier direct normalization attempts hit the heartbeat limit while exposing the generated pair-pattern bind; none was an OOM. The replacement exposes the exact Result bind using a named generic inversion lemma, avoiding that normalization. Failed snapshots are retained and are not counted as checked targets. No held commitment-layer work was performed.
