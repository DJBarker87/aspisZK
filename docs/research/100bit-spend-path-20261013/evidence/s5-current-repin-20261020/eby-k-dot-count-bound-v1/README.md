# EbyK count-indexed accumulator bound

This focused Lean result establishes a count-indexed bound for the actual successful `EbyKPushDotBackend.pushWithDotBackend` source model. If every accumulator lane is at most `k * 2^34` and `k < 4096`, then each lane is strictly below `2^46` before the call; the actual source guard supplies `k < 4096`. A successful step advances the state to a bound of `(k+1) * 2^34`, and an accepted trace preserves the invariant through at most count 4096.

At the 4095-to-4096 edge the theorem claims only `≤ 2^46` for the resulting accumulator. It does not claim that state is strictly below `2^46`. A subsequent successful push again requires the source guard `count < 4096`, so the strict pre-call bound is derived only for calls that can pass that guard.

The remaining caller boundary is the exact outer Rust traversal (`weights::pair` / `finish_query_dot`) to `AcceptedPushTrace`, including initialization and traversal lengths. This packet does not claim that mapping is closed.

The source, receipt, command, preflight, timing, reservation, and admission records are included. No compiled object is included. The theorem imports the accepted per-call product-update module from the adjacent `eby-k-qraw-dot-product-update-v2` packet.
