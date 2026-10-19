# Actual semantic source loops compute the sumcheck polynomial operations

The generated reverse-Horner loop is proved by a decreasing Usize measure and suffix polynomial invariant. Starting from the generated zero constant and canonical decoded coefficients/challenge, the actual semantic_value call succeeds, returns canonical coordinates and decodes to the corresponding degree-at-most-27 polynomial evaluated at that challenge. Exact checked subtraction, coefficient/challenge reads, multiplication and addition are derived in the proof; they are not operation-success premises.

The boundary wrapper reads coefficient zero as its seed and composes the already proved increasing generated loop. Its result is exactly p(0)+p(1). Coefficient zero occurs both as the seed and in the sum, as in the actual source. Both wrappers consume the actual generated candidate functions rather than arbitrary arithmetic callbacks or a handwritten loop.

Focused Lean 4.32 checks exit 0 in 2.37s and 4.52s, with peak RSS 2,587,983,872 and 2,528,362,496 bytes, respectively; process swaps are zero. All four printed theorem reports contain only propext, Classical.choice and Quot.sound. Exact source/object/import pins, commands, source revisions and logs are retained.

These are working checks for the isolated candidate source extraction in source-proof-loop-extraction-20261019. Canonical coefficient/challenge inputs and round<10 remain explicit at these operation leaves. Their accepted-decoder/sampler provenance and concrete round-model/caller composition are separate consuming steps. Production source remains unchanged. This is neither a clean unified release build nor the complete 100-bit spend theorem.
